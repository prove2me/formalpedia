-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_scale_ratio_gap
-- name    : AvramDividend.Classical.p2m81_bv_scale_ratio_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T08:00:13.036954+00:00
-- url     : https://prove2.me/theorems/8474a61e-24a0-4279-a284-f296dfe1967e
-- title:
--   BV scale ratio eventually exceeds half the reciprocal drift
-- statement:
--   For a bounded-variation spectrally negative Levy process with positive drift, the Laplace exponent eventually exceeds any fixed q on positive arguments, and the ratio beta/(psi(beta)-q) eventually exceeds 1/(2*drift). Standing-free helper for parent fc6b315a: from Proved bv_exponent_gap_div_tendsto_zero derive psi(t)/t -> drift and (psi(t)-q)/t -> drift, then trap and invert to the ratio lower bound used in the Tauberian contradiction.
-- source:
--   Decomposition child C of fc6b315a. Uses only Proved public bv_exponent_gap_div_tendsto_zero at pinned rev; no drift_pos/esscher_pointwise/renewal_package imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_scale_ratio_gap {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (q : ℝ) (hd : 0 < X.drift) :
    (∀ᶠ θ in atTop, 0 < θ ∧ q < X.ψ θ) ∧ ∀ᶠ β in atTop, 1 / (2 * X.drift) < β / (X.ψ β - q) := by sorry
