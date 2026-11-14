-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
-- name    : AvramDividend.Classical.avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:23:01.113548+00:00
-- url     : https://prove2.me/theorems/5c4dd041-5b74-484f-b47e-e4bfb8059865
-- title:
--   Original BV full negative-mark small-jump Lipschitz and large-jump bounded envelope is L1
-- statement:
--   For the original spectrally negative bounded-variation Levy measure, small negative jump first moment integrability implies integrability of a piecewise full negative-mark envelope: local Lipschitz times mark size for small claims and a constant for large claims, provided a positive multiple of the truncated first moment dominates both pieces. This is the missing L1 domination ingredient for genuine finite-cap full unmasked stochastic compensation with w(0) allowed positive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε L M K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2)) :
    Integrable (fun z : ℝ =>
      if -(ε / 2) ≤ z then L * |z| else 2 * M)
      (X.ν.restrict (Iio (0 : ℝ))) := by sorry
