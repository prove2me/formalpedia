-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_killed_scale_martingale_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_killed_scale_martingale_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T06:49:23.155879+00:00
-- url     : https://prove2.me/theorems/3f2f02d1-3fb3-4ba5-89c1-87ba7c6dc21a
-- title:
--   Standing-free BV killed q-scale martingale from Esscher root (public)
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive Esscher root X.psi phi = q, the killed discounted q-scale process is a true martingale, with no Standing assumption. This is the standing-free analogue of avram_ws01b_bv_killed_scale_martingale, replacing Standing by the root hypothesis; it is the single missing premise for the standing-free BV clipped-grid killed optional stopping equality.
-- source:
--   Standing-free BV killed martingale from Esscher root: positive-root harmonicity replaces Standing in the BV killed q-scale martingale. Parent AvramDividend.Classical.p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing (db3e52be) replays accepted standing proofs 1870b0f3 and e7f81c41 with every other step already Proved standing-free; this child is the only step with no standing-free form. Near-misses ab64adeb (standing BV) and dba19614 (UBV) are inapplicable by hypothesis mismatch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_killed_scale_martingale_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by sorry
