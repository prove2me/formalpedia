-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_origin_drift_product_one
-- name    : AvramDividend.Classical.bv_scale_origin_drift_product_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:34:10.236186+00:00
-- url     : https://prove2.me/theorems/1f127d6f-7dec-41d4-b5a4-ff4ffbefe825
-- title:
--   Bounded-variation scale-function origin normalises the physical drift exactly
-- statement:
--   For a standing spectrally negative Levy process of bounded variation and positive discount q, the physical drift times the q-scale function at the origin equals one. This gives the boundary normalisation that cancels the drift boundary term in the Laplace transform of the first-order generator, and avoids using the Gaussian second-derivative normalisation.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lévy scale-function boundary formula and Lemma 4.

import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_scale_origin_drift_product_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    X.drift * W 0 = 1 := by sorry

end AvramDividend.Classical
