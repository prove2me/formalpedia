-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_lipschitzOn_positive_compact_ws01b
-- name    : AvramDividend.Classical.bv_scale_lipschitzOn_positive_compact_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:18:06.098857+00:00
-- url     : https://prove2.me/theorems/9d40e792-7e10-40eb-a7db-874a7fdda380
-- title:
--   Uniform local Lipschitz regularity of BV q-scale on positive reserve strips
-- statement:
--   For any standing bounded-variation spectrally negative Lévy process and positive discount, the q-scale function is Lipschitz on each compact reserve strip [epsilon,a] with epsilon strictly positive. No continuity or smoothness is assumed at the origin, where W(0) is nonzero.
-- source:
--   Analytically follows from the already-Proved standing BV C1 positive-axis regularity and the compact-convex C1-to-Lipschitz theorem in the pinned Mathlib. Provides a boundary-safe local estimate for BV sample-path chain-rule localisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_lipschitzOn_positive_compact_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (ε a : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ≥0, LipschitzOnWith K W (Icc ε a) := by sorry
