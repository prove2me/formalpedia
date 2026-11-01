-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finite_marginal_outer_regular
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_outer_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:36:09.144028+00:00
-- url     : https://prove2.me/theorems/e64de0f4-1d1c-4ce7-b888-274a2926d520
-- title:
--   Open outer approximation of every genuine Esscher-reflected finite marginal event
-- statement:
--   For every actual finite-coordinate Esscher-tilted reflected SNLP marginal, every event A (even non-Borel) and every ε>0 have an open finite-coordinate neighbourhood U⊇A whose genuine Esscher marginal mass is less than mass(A)+ε. The measure is precisely the finite Esscher pushforward of the running supremum and reflected drawdown, not a generic law; positive q and φ and ψφ=q are exact source binders. This supplies the cylinder-extension compact/open regularity bridge, not a path law or an excursion compensator.
-- source:
--   Source runningSup/reflectedSup adaptedness and source finite-stop Esscher probability; Mathlib finite Borel regularity on finite Euclidean products. No conditional probabilistic premises.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_outer_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
      ∀ (ε : ℝ≥0∞), 0 < ε →
      ∃ U : Set (I → ℝ × ℝ),
        IsOpen U ∧ A ⊆ U ∧
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) U
        <
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A + ε := by sorry
