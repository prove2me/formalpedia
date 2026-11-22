-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_driftpos_eventual_psi_above_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_driftpos_eventual_psi_above_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:10:47.009732+00:00
-- url     : https://prove2.me/theorems/f9712bc7-cdb7-4d86-9769-f8f81b5ff37d
-- title:
--   Drift-positive BV Laplace exponent eventually exceeds every positive discount
-- statement:
--   For a bounded-variation spectrally negative Levy process with strictly positive drift, the Laplace exponent eventually exceeds every positive discount q, with no Standing assumption. Public helper isolating the standing-free eventual-growth argument (replay of psi_eventually_gt_of_boundedVariation with root-derived drift); parent p2m81_bv_root_eventual_psi_above_no_standing_public supplies drift positivity from its Laplace root.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_driftpos_eventual_psi_above_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hdrift : 0 < X.drift)
    (hBV : X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry
