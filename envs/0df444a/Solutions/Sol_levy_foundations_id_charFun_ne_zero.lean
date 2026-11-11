-- Prove2me | solution 1 for levy_foundations_id_charFun_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:07:07.041884+00:00
-- url     : https://prove2.me/submissions/1b98636d-9585-4be6-ad65-a50530b4d46b

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Theorems.Thm_levy_foundations_id_charFun_zero_halves

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∀ ξ : ℝ, charFun μ ξ ≠ 0 := by
  intro ξ hzero
  have hhalves : ∀ n : ℕ,
      charFun μ (ξ * (1 / 2 : ℝ) ^ n) = 0 := by
    intro n
    induction n with
    | zero =>
        simpa using hzero
    | succ n ih =>
        have harg :
            2 * (ξ * (1 / 2 : ℝ) ^ (n + 1)) =
              ξ * (1 / 2 : ℝ) ^ n := by
          rw [pow_succ]
          ring
        have hstep := levy_foundations_id_charFun_zero_halves hμ
          (ξ * (1 / 2 : ℝ) ^ (n + 1))
        apply hstep
        rw [harg]
        exact ih
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled : Tendsto (fun n : ℕ => ξ * (1 / 2 : ℝ) ^ n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hlim : Tendsto
      (fun n : ℕ => charFun μ (ξ * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 (charFun μ 0)) :=
    (continuous_charFun.tendsto 0).comp hscaled
  have hzeroLimit : Tendsto
      (fun n : ℕ => charFun μ (ξ * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [hhalves] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have h0 : charFun μ 0 = (0 : ℂ) :=
    tendsto_nhds_unique hlim hzeroLimit
  have hone : charFun μ 0 = (1 : ℂ) := by
    simpa [charFun_zero]
  exact one_ne_zero (hone.symm.trans h0)
