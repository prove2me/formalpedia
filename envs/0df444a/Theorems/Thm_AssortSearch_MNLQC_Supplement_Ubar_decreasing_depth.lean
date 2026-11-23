-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_Ubar_decreasing_depth
-- name    : AssortSearch.MNLQC.Supplement.Ubar_decreasing_depth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:22:05.790486+00:00
-- url     : https://prove2.me/theorems/1e6c6d7c-2ee5-4d7a-a15e-4108b4c283fc
-- title:
--   §4.3 — the overlapping search threshold $\bar U(S)$ strictly decreases as the assortment grows
-- statement:
--   Let $v_1,\dots,v_n>0$ be the variants' preferences, $\mu>0$ the Gumbel scale and $b>0$ the search cost of the overlapping assortment model. For an assortment $S\subsetneq N$, let $\bar U(S)$ be the consumer's search threshold, the unique solution of (4):
--   $$\int_{\bar U(S)}^\infty(\bar y-\bar U(S))\,w(\bar y,S)\,d\bar y=b,$$
--   where $w(\cdot,S)$ is the density of the best utility among the variants outside $S$. If $S\subsetneq S'\subsetneq N$, then
--   $$\bar U(S')<\bar U(S).$$
--
--   The more variants the retailer carries, the less a consumer expects to find outside the assortment, and the lower the utility at which she stops searching. The paper states this in §4.3 without proof. It is why the overlapping model is harder than the independent one, where the threshold is fixed, and it drives the overlapping case of Theorem 7.
--
--   **Formalization Note** $\bar U(S)$ is `AssortSearch.FullAssort.Ubar`. Popular assortments of depths $x<x'<n$ are the special case $S=\{1,\dots,x\}$, $S'=\{1,\dots,x'\}$. $\bar U(N)$ is not defined, since there is no search at the full assortment, so $S'\ne N$.
--
--   Differences from the source:
--   - generalization: "Ū(S) is decreasing in the depth of the assortment" → Ū(S′) < Ū(S) for every strictly nested pair S ⊊ S′ ⊊ N; reason: deepening the assortment adds variants; the depth form x < x′ < n is the special case of popular sets, and the decrease is strict because every v_i > 0
--   - encoding: the threshold Ū(S′) → hypotheses S′ ≠ N and b > 0; reason: Ū is defined only for assortments with a variant outside and positive search cost; only undefined cases are excluded
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 17 (PDF 19), §4.3, first sentence

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- §4.3 (p. 17): in the overlapping assortment model the search threshold `Ū(S)` strictly
decreases as the assortment grows: for `S ⊊ S' ⊊ N` and `b > 0`, `Ū(S') < Ū(S)`. -/
theorem Ubar_decreasing_depth {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (S S' : Finset (Fin n)) (hSS' : S ⊂ S') (hS' : S' ≠ Finset.univ) (b : ℝ) (hb : 0 < b) :
    AssortSearch.FullAssort.Ubar μ v S' b < AssortSearch.FullAssort.Ubar μ v S b := by sorry

end AssortSearch.MNLQC.Supplement
