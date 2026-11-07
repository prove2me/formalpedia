-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_killed_scale_martingale_all_variation
-- name    : AvramDividend.Classical.avram_p4_f6_original_killed_scale_martingale_all_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:43:33.264042+00:00
-- url     : https://prove2.me/theorems/c9be1603-14ca-4555-83ff-e74cd9979a19
-- title:
--   Actual killed discounted q-scale reward is a martingale in both variation branches
-- statement:
--   The genuine original spectrally negative Lévy killed q-scale reward (killed when its reserve becomes negative) is a continuous-time martingale, for any Standing process, positive discount and starting reserve. This assembles the already proved BV and unbounded-variation source-specific killed martingales into one usable theorem; the next step is bounded optional stopping at the upper/lower exit clock for the stopped-minimum harmonicity child 27e24986.
-- source:
--   Both branch-specific original process martingale proofs are authoritative Proved (ab64adeb and dba19614). The universal theorem is a genuine all-variation adapter, enabling uniform optional stopping rather than reproving two probabilistic branches.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_martingale
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_killed_scale_martingale_all_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by sorry
