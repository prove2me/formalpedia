-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_iia_overlapping
-- name    : AssortSearch.MNLQC.Supplement.iia_overlapping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:22:34.428557+00:00
-- url     : https://prove2.me/theorems/36d7f12e-74f7-4ea3-ac0b-951e2f2ba938
-- title:
--   IIA between product variants in the overlapping model: $q_i^{so}(x)/q_j^{so}(x)=v_i/v_j$
-- statement:
--   Let $v_1,\dots,v_n>0$ and $v_0>0$ be the preferences, $\mu>0$ the Gumbel scale and $b>0$ the search cost of the overlapping assortment model. Consider the assortment of depth $x$, i.e. the $x$ most popular variants, with demands
--   $$q_i^{so}(x)=q_i^m(x)\,\big(1-H(\bar U(x),x)\big)$$
--   from Theorem 3; at the full assortment ($x\ge n$) there is no search and $q_i^{so}(x)=q_i^m(x)$. Then for any two product variants $i,j$ in the assortment,
--   $$\frac{q_i^{so}(x)}{q_j^{so}(x)}=\frac{v_i}{v_j}.$$
--
--   The independence of irrelevant alternatives thus holds between product variants in the overlapping model, as in the no-search and independent models. As a result, iterative assortment planning estimates the relative preferences of product variants correctly.
--
--   **Formalization Note** The demands are `demandOv`, i.e. `AssortSearch.FullAssort.demandSO` on `popularSet n x`; variants are 0-based, so $i,j$ in the assortment means index $<x$.
--
--   Differences from the source:
--   - encoding: "for i, j ≠ 0", two product variants in an assortment → indices i, j with i, j < x, the variants of the depth-x assortment; reason: the demand ratio concerns offered variants; 0-based indexing
--   - encoding: q^so(x), the overlapping demand → Theorem 3's closed form (FullAssort.demandSO), with no search when x ≥ n; reason: Theorem 3 (milestone theorem_3) proves the closed form equals the choice probability; at the full assortment the paper's model has no search
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 21 (PDF 23), §5.1, IIA display for q^so

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- IIA among product variants in the overlapping assortment model (p. 21):
`q_i^so(x) / q_j^so(x) = v_i / v_j` for product variants `i, j` of the assortment of depth `x`. -/
theorem iia_overlapping {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hμ : 0 < μ) (hb : 0 < b) (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (x : ℕ) (i j : Fin n) (hi : i.val < x) (hj : j.val < x) :
    demandOv μ b v v0 x i / demandOv μ b v v0 x j = v i / v j := by sorry

end AssortSearch.MNLQC.Supplement
