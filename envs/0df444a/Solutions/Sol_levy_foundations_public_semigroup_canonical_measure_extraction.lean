-- Prove2me | solution 1 for levy_foundations_public_semigroup_canonical_measure_extraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:40:56.933449+00:00
-- url     : https://prove2.me/submissions/cec5585a-2b21-4cdf-8a48-acfea906f5f5

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_levy_foundations_public_semigroup_tilted_mass_along_seq
import Theorems.Thm_levy_foundations_public_semigroup_scaled_largeSet_tail_bound
import Theorems.Thm_levy_foundations_public_finite_tight_subsequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Canonical tilted-measure extraction from bounded mass and uniform tails. -/
theorem solution (S : ProbabilityTheory.ConvolutionSemigroup) :
    ∃ (η : Measure ℝ) (_ : IsFiniteMeasure η) (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ), f 0 = 0 →
        Tendsto (fun n => ∫ x, f x ∂(S.tiltedScaledMeasure (t_seq n)))
          atTop (𝓝 (∫ x, f x ∂η)) := by
  set s : ℕ → {t : ℝ // 0 < t} := fun n => ⟨1/(n+2), by positivity⟩ with hs_def
  have hs_tendsto : Tendsto (fun n => (s n).val) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun n => ?_)
    simp [s, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨Cmass, _, hCmass_ev⟩ :=
    levy_foundations_public_semigroup_tilted_mass_along_seq S hs_tendsto
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hCmass_ev
  let t_seq : ℕ → {t : ℝ // 0 < t} := fun n => s (n + n₀)
  have ht_seq_tendsto : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) :=
    hs_tendsto.comp (tendsto_add_atTop_nat n₀)
  let ν : ℕ → Measure ℝ := fun n => S.tiltedScaledMeasure (t_seq n)
  have hmass : ∀ n, ν n Set.univ ≤ (Cmass : ℝ≥0∞) :=
    fun n => hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  have htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ n, ν n (largeSet R) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨R, hR1, hR⟩ :=
      levy_foundations_public_semigroup_scaled_largeSet_tail_bound S ε hε
    refine ⟨R, hR1, fun n => ?_⟩
    have hfg : Set.EqOn (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)))
        (fun _ => (1 : ℝ≥0∞)) (largeSet R) := by
      intro x hx
      have hx1 : (1 : ℝ) ≤ x ^ 2 := by
        nlinarith [sq_abs x, abs_nonneg x, hR1, (show R ≤ |x| from hx)]
      simp [min_eq_left hx1]
    have hmeas_large : MeasurableSet (largeSet R) := by
      change MeasurableSet {x : ℝ | R ≤ |x|}
      exact measurableSet_le measurable_const continuous_abs.measurable
    have heq : S.tiltedScaledMeasure (t_seq n) (largeSet R) =
        S.scaledMeasure (t_seq n) (largeSet R) := by
      rw [show S.tiltedScaledMeasure (t_seq n) =
          (S.scaledMeasure (t_seq n)).withDensity
            (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
        withDensity_apply _ hmeas_large,
        setLIntegral_congr_fun hmeas_large hfg, setLIntegral_one]
    rw [heq]
    change ENNReal.ofReal (t_seq n).val⁻¹ *
      (S.measure (t_seq n) : Measure ℝ) (largeSet R) ≤ ENNReal.ofReal ε
    rw [show (S.measure (t_seq n) : Measure ℝ) (largeSet R) =
      ENNReal.ofReal ((S.measure (t_seq n) : Measure ℝ) (largeSet R)).toReal from
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (t_seq n).prop))]
    exact ENNReal.ofReal_le_ofReal (hR (t_seq n))
  obtain ⟨η, hη, φ, hφ_mono, hconv⟩ :=
    levy_foundations_public_finite_tight_subsequence ν Cmass hmass htail
  refine ⟨η, hη, t_seq ∘ φ, ht_seq_tendsto.comp hφ_mono.tendsto_atTop, ?_⟩
  intro f hf0
  exact hconv f hf0
