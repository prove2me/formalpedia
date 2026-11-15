-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
-- name    : AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:26:42.128889+00:00
-- url     : https://prove2.me/theorems/7da989dc-8b1b-4914-ad8a-b4cb458963d4
-- title:
--   The genuine original intrinsic compensated smallmark Lévy source is a finite marked step process plus drift on every bounded horizon
-- statement:
--   For any actual finite-negative-activity spectrally negative Lévy path X on its original probability space and any intrinsic residual smallmark source Jsmall satisfying only the a.e. all-time cutoff limit, on one P-conull set and for every bounded physical horizon T there is a SINGLE finite set S of true X jump times up to T such that for all t≤T, Jsmall(t) equals their right-inclusive chronological physical small-negative-mark step sum minus elapsed time times the true complete signed smallmark compensator. This source representation includes the true ruin-contact jump, yields a càdlàg finite step plus drift path, and enables the original Itô-Meyer marked channel without auxiliary Poisson processes or postruin paths.
-- source:
--   Proved original finite true-jump support a30, B24 all-time Jsmall finite actual jump path, B24 horizon-support marked step sum identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        ∀ t : ℝ≥0, t ≤ T →
          Jsmall t ω =
            (∑ u ∈ S, if u ≤ t then
              (if -1 < X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
                  X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
               then X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0)
             else 0) -
            (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by sorry
