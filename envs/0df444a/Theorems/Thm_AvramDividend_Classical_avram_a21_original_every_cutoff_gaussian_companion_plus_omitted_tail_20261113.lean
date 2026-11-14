-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_every_cutoff_gaussian_companion_plus_omitted_tail_20261113
-- name    : AvramDividend.Classical.avram_a21_original_every_cutoff_gaussian_companion_plus_omitted_tail_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:47:15.000132+00:00
-- url     : https://prove2.me/theorems/e1ca7c65-1783-49dc-b0d4-b0564759295b
-- title:
--   Original every-cutoff intrinsic Gaussian residual equals same-source Gaussian companion plus omitted small mark tail
-- statement:
--   On the SAME original sample path, assuming the source Gaussian companion decomposition at cutoff zero, every finite cutoff residual equals drift-centred Gaussian companion plus omitted compensated negative jump tail Jsmall-Jn. This identifies omitted-versus-retained terms exactly and prevents the false independence of R0 and retained Jn. Holds for every n and t almost surely and is direct consequence of Proved original Rn=R0-Jn.
-- source:
--   Proved original source residual finite-cutoff retained subtractions bfc8537f, and source Gaussian companion decomposition premise of ca457ff7. Elementary real ring arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_every_cutoff_gaussian_companion_plus_omitted_tail_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hDecomp : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        (Y.X t ω - (t : ℝ) * Y.c) +
          (Jsmall t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by sorry
