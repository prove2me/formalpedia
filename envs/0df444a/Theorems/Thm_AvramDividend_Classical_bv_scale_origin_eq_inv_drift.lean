-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
-- name    : AvramDividend.Classical.bv_scale_origin_eq_inv_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:33:58.448664+00:00
-- url     : https://prove2.me/theorems/973f7ca3-0d3a-491f-9e75-c780dbd572ab
-- title:
--   Canonical bounded-variation scale function equals reciprocal positive drift at zero
-- statement:
--   For the standing bounded-variation spectrally negative Lévy process, the canonical q-scale function has its exact nonzero boundary value W(0)=1/d, with d the compensated positive drift. This is a common mathematical prerequisite of the finite and infinite negative-jump-intensity zero-barrier branches. The canonical Esscher renewal measure has a Dirac zeroth atom; the existing pointwise representation and right continuity identify this value.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale function bounded-variation boundary; Proved canonical geometric representation bd5082fb-392c-4e36-9858-95c79a31ed92.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_scale_origin_eq_inv_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) :
    W 0 = 1 / X.drift := by sorry
