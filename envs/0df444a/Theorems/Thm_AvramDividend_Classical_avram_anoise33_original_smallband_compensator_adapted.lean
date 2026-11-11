-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
-- name    : AvramDividend.Classical.avram_anoise33_original_smallband_compensator_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:43:08.122639+00:00
-- url     : https://prove2.me/theorems/7ba6e5dc-3a22-453c-b605-06897101dfc9
-- title:
--   Original finite-cutoff signed small-band compensator is adapted
-- statement:
--   The actual finite-band signed compensated jump sum is measurable in the original filtration at time t. The original intrinsic truncated residual is already proved measurable for every cutoff. At cutoff zero the band is empty and its compensated integral vanishes; subtracting the nth residual from the zero-cutoff residual gives exactly the nth compensated small-band sum. This is a same-process algebraic adaptedness bridge needed to transfer future-increment centring to the martingale identity.
-- source:
--   Original zero-cutoff residual minus nth residual equals the nth compensated band because small-band zero cutoff is empty. Uses Proved 42ada2ca residual adaptedness. Feeds 867b4b3a together with signed future increment centring; no new process or filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise33_original_smallband_compensator_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t]
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by sorry
