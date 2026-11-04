-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_summable_discounted_rightjump_residual_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_summable_discounted_rightjump_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:48.742325+00:00
-- url     : https://prove2.me/theorems/4a851201-7832-454b-a74a-d4bd65dfbfab
-- title:
--   Original process summable countable payment residual cannot increase the HJB budget
-- statement:
--   For an arbitrary (possibly countable or infinite) set of original admissible payment times, the original source jump inequality forces the total discounted signed dividend-versus-secant remainder to be nonpositive whenever the actual remainder series is summable. This is the countable-atom sign interface needed before showing existence of the stochastic correction.
-- source:
--   Original P4-F jump-budget hypothesis, true riskProcess/rightLimit; Mathlib pinned tsum_nonpos; unconditional once explicit summability is supplied.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_summable_discounted_rightjump_residual_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (A : Set ℝ≥0)
    (helig : ∀ t ∈ A, t = 0 ∨
      (t : ℝ≥0∞) < ruinTime X x D ω)
    (R : A → ℝ)
    (hR : ∀ a : A, R a =
      Real.exp (-(q * (a.1 : ℝ))) *
        ((rightLimit D a.1 ω - D a.1 ω) -
          (w (riskProcess X x D a.1 ω) -
            w (riskProcess X x D a.1 ω -
              (rightLimit D a.1 ω - D a.1 ω)))))
    (hSum : Summable R) :
    (∑' a : A, R a) ≤ 0 := by sorry
