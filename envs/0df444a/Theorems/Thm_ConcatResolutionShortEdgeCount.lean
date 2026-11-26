-- Prove2me | Theorems.Thm_ConcatResolutionShortEdgeCount
-- name    : ConcatResolutionShortEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:21.494596+00:00
-- url     : https://prove2.me/theorems/76cad5cd-ffdc-59bb-a6d8-785adf811280
-- title:
--   Concat Resolution Short Edge Count: Concat Resolution Short Edge Count
-- statement:
--   **Short-edge counts are additive across a glued resolution.** `ConcatGeodesicResolution`
--   resolves a concatenation `η₁ * η₂` by the spliced breakpoint sequence `R i = r₁ i` for `i ≤ K₁` and
--   `R i = L + r₂ (i - K₁)` for `i > K₁`, where `L = length(η₁) = r₁ K₁` and `r₂ 0 = 0`. This lemma
--   says that the number of short (length `< δ`) edges of `R` is *exactly* the sum of the numbers of
--   short edges of `r₁` and of `r₂`: the two index blocks `{1,…,K₁}` and `{K₁+1,…,K₁+K₂}` partition
--   `{1,…,K₁+K₂}`, the shift `L` cancels out of every edge difference on the upper block, and the one
--   straddling index `i = K₁+1` gives the edge `L + r₂ 1 - r₁ K₁ = r₂ 1 - r₂ 0` because `r₁ K₁ = L`
--   and `r₂ 0 = 0`. `ConcatGeodesicResolution` asserts only that the glued object *is* a resolution; it
--   says nothing about edge counts, which is the entire content here. Applied with `K₂ = 1` it gives
--   the "at most one extra short edge for the single closing geodesic edge" bound that a basic cut's
--   output needs.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatResolutionShortEdgeCount.lean#L17-L77
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatResolutionShortEdgeCount.lean#L17-L77

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ConcatResolutionShortEdgeCount
set_option autoImplicit false
open Set

theorem ConcatResolutionShortEdgeCount (K₁ K₂ : ℕ) (r₁ r₂ R : ℕ → ℝ) (L δ : ℝ)
    (hL : r₁ K₁ = L) (hz : r₂ 0 = 0)
    (hR : ∀ i : ℕ, R i = if i ≤ K₁ then r₁ i else L + r₂ (i - K₁)) :
    ((Finset.Icc 1 (K₁ + K₂)).filter (fun i => R i - R (i - 1) < δ)).card
      = ((Finset.Icc 1 K₁).filter (fun j => r₁ j - r₁ (j - 1) < δ)).card
        + ((Finset.Icc 1 K₂).filter (fun j => r₂ j - r₂ (j - 1) < δ)).card := by sorry
