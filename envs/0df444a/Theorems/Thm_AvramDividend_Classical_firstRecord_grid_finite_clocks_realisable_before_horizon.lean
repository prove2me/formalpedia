-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_grid_finite_clocks_realisable_before_horizon
-- name    : AvramDividend.Classical.firstRecord_grid_finite_clocks_realisable_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:33:44.305764+00:00
-- url     : https://prove2.me/theorems/f5461511-bd4c-43de-bd89-e97a39d81b5f
-- title:
--   Finite record clocks below a horizon admit an ordered real-time grid
-- statement:
--   If the first upcrossing of record level b+N h lies strictly before a finite horizon T and h is nonnegative, then all lower indexed upcrossing clocks are finite. They can be represented by nonnegative real times u_k, ordered on consecutive grid steps and with u_N strictly before T. This supplies the finite-clock witness required by the stopped N-cell and terminal-cell upper estimates.
-- source:
--   Monotonicity of strict upcrossing infima in the threshold and the ENNReal.toNNReal coercion equivalence for finite extended times.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Nat.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.firstRecord_grid_finite_clocks_realisable_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b h : ℝ) (hh : 0 ≤ h) (T : ℝ≥0) (N : ℕ)
    (hN : (⨅ (r : ℝ≥0)
      (_ : b + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
      (T : ℝ≥0∞)) :
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))) ∧
      (∀ k : ℕ, k < N → (u k : ℝ) ≤ (u (k + 1) : ℝ)) ∧
      (u N : ℝ≥0∞) < (T : ℝ≥0∞) := by sorry
