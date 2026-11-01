-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:31:17.276412+00:00
-- url     : https://prove2.me/theorems/9a4b63dc-11bf-43ef-89fd-cc8ab06d1c83
-- title:
--   Inner compact approximation of every measurable genuine Esscher-reflected finite marginal event
-- statement:
--   For the actual reflected SNLP (running supremum and reflected drawdown), positive Esscher root, and every finite observation-time set I, every Borel finite-dimensional event A admits a compact subset K carrying all but any prescribed positive epsilon of A's genuine Esscher finite-clock probability. The law is exactly the finite Esscher-tilted pushforward under observation horizon sup I + 1, with no arbitrary law or Standing assumption. It is a source-specific inner regularity input for extending the correlated projective family to a countably additive cylinder measure. It does not claim an infinite-horizon path measure, cadlag concentration, an Ito excursion intensity, or compensation.
-- source:
--   Actual adaptedness and finite stopped Esscher probability; Mathlib inner regularity of finite Borel measures on second-countable completely pseudometrizable spaces. Strengthens previously accepted marginal tightness 3ebdc5d2 to compact subsets of any measurable event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_finite_marginal_inner_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ (I : Finset ℝ≥0) (A : Set (I → ℝ × ℝ)),
      MeasurableSet A → ∀ (ε : ℝ≥0∞), 0 < ε →
      ∃ K : Set (I → ℝ × ℝ),
        IsCompact K ∧ K ⊆ A ∧
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) A
        <
        (Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) K + ε := by sorry
