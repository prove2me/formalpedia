-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
-- name    : AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:36:55.313167+00:00
-- url     : https://prove2.me/theorems/1b617de2-405f-444b-8c59-98fdee3fe564
-- title:
--   Genuine stopped original Lévy jump occupation and canonical compensator vanish on every deterministic predictable time atom
-- statement:
--   For the actual original spectrally negative Lévy process X and exactly its sample-path jump kernel on the unchanged right-continuous filtration, the stopped predictable occupation measure M.restrict S and the canonical finite-horizon Lebesgue-time by original-P by X.ν product measure both charge zero mass to every deterministic-time predictable marked slice. The result holds at arbitrary deterministic t, Borel negative or positive B, any measurable predictable time-history slice, any restriction S, and all finite horizons T; the proof invokes actual no-fixed-time-jump and source sigma-finite Lévy intensity. It supplies exact endpoint localisation equalities but does not assert future negative mark intensity.
-- source:
--   Source-bound endpoint localisation stronger than the previously proved t=0 hBot 41f9. Uses actual original no-fixed-time marks 3bec after unchanged-path rightCont lift e58, canonical finite-horizon μ 16857 and intrinsic X.ν sigma-finiteness f2f. Every deterministic-time singleton of mapped truncated Lebesgue has zero mass; both sides vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ D : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] D →
        μ D = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) D) ∧
      (∀ (t : ℝ≥0) (A : Set Ω),
        MeasurableSet[𝓕.rightCont.predictable] ({t} ×ˢ A) →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (({t} ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (({t} ×ˢ A) ×ˢ B) ∧
        MT (({t} ×ˢ A) ×ˢ B) = 0) := by sorry
