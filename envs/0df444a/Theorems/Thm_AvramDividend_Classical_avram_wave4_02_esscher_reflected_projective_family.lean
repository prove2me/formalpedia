-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_projective_family
-- name    : AvramDividend.Classical.avram_wave4_02_esscher_reflected_projective_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:11:19.683517+00:00
-- url     : https://prove2.me/theorems/03188b99-d5f5-4cb9-acda-eef64e0dd725
-- title:
--   Actual Esscher-reflected Lévy pair determines a projective family of finite-dimensional measures
-- statement:
--   For the actual spectrally negative Lévy source X and its positive q-root Esscher density, the family indexed by all finite time sets I, obtained by pushing the genuine finite Esscher law at terminal time (sup I)+1 through the joint path coordinates (runningSup X, reflectedSup X), is a projective measure family under restriction from I to J subset I. This does not assert all-horizon extension, Poisson excursions or an Itô intensity.
-- source:
--   The accepted actual source finite-dimensional Esscher law 8a1e0b63 (submission d4307f98) and pinned Mathlib IsProjectiveMeasureFamily; source adaptedness of the record and drawdown; Finset.sup_mono and Measure.map_map.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_esscher_reflected_finset_projective_law
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_esscher_reflected_projective_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => ℝ × ℝ)
      (fun I : Finset ℝ≥0 =>
        Measure.map
          (fun ω : Ω => fun i : I =>
            (runningSup X (i : ℝ≥0) ω, reflectedSup X (i : ℝ≥0) ω))
          (P.withDensity (fun ω => ENNReal.ofReal
            (Real.exp (φ * X.X ((I.sup id) + 1) ω -
              ((((I.sup id) + 1 : ℝ≥0) : ℝ)) * X.ψ φ))))) := by sorry
