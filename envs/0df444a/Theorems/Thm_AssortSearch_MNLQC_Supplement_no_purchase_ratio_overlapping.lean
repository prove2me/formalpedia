-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_no_purchase_ratio_overlapping
-- name    : AssortSearch.MNLQC.Supplement.no_purchase_ratio_overlapping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:23:09.575443+00:00
-- url     : https://prove2.me/theorems/84dc27e6-0374-4f28-8584-b28f60a10766
-- title:
--   No-purchase ratio in the overlapping model: $q_0^{so}(x)/q_i^{so}(x)$ with the depth-dependent threshold $\bar U(x)$
-- statement:
--   Let $v_1,\dots,v_n>0$ and $v_0>0$ be the preferences, $\mu>0$ the Gumbel scale and $b>0$ the search cost of the overlapping assortment model. Consider an assortment of depth $x<n$ and write $\bar U(x)$ for its search threshold (Theorem 3) and $H(\bar U(x),x)=\exp\big(-\lambda(v_0+\sum_{j\le x}v_j)\big)$ with $\lambda=\exp[-(\bar U(x)/\mu+\gamma)]$. Let $q_i^{so}(x)=q_i^m(x)(1-H(\bar U(x),x))$ be the variants' demands and $q_0^{so}(x)=1-\sum_{i\le x}q_i^{so}(x)$ the no-purchase demand. Then for every product variant $i\le x$,
--   $$\frac{q_0^{so}(x)}{q_i^{so}(x)}=\frac{q_0^m(x)+\sum_{j\le x}q_j^m(x)\,H(\bar U(x),x)}{q_i^m(x)\,\big(1-H(\bar U(x),x)\big)},$$
--   where $q_j^m(x)=v_j/(v_0+\sum_{k\le x}v_k)$ and $q_0^m(x)=v_0/(v_0+\sum_{k\le x}v_k)$ are the MNL shares (2).
--
--   The ratio depends on the assortment through both the shares and the threshold. So the overlapping model, like the independent one, violates IIA with respect to the no-purchase variant. This is the source of the bias described in Theorem 7.
--
--   **Formalization Note** $q_0^{so}$ is `demandNoPurchaseOv`, defined by the normalisation (14). $q_0^m(x)$ is the published `AssortSearch.HeurEq.shareNoPurchase`. Variants are 0-based.
--
--   Differences from the source:
--   - reading: the independent-model display with H(Ū, x), followed by "and the same holds with the overlapping assortment model" → the same display with H(Ū(x), x), Ū(x) the overlapping threshold of the depth-x assortment; reason: in the overlapping model the threshold depends on the assortment (Theorem 3)
--   - encoding: any assortment x → x < n; reason: Ū(x) is defined only when some variant is outside the assortment; at x = n there is no search and H(Ū(n), n) is undefined. Only undefined cases are excluded
--   - encoding: q_0^so(x) → 1 − ∑_{i≤x} q_i^so(x); reason: the no-purchase demand of the retailer, normalisation (14); consumers who search are lost to the retailer
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 21–22 (PDF 23–24), §5.1, no-purchase ratio display and "and the same holds with the overlapping assortment model"

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- The relative preference of the no-purchase variant in the overlapping assortment model
(pp. 21–22): for an assortment of depth `x < n` and a product variant `i` in it,
`q_0^so(x) / q_i^so(x) = (q_0^m(x) + ∑_{j ≤ x} q_j^m(x) H(Ū(x), x)) / (q_i^m(x) (1 − H(Ū(x), x)))`. -/
theorem no_purchase_ratio_overlapping {n : ℕ} (μ b : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hμ : 0 < μ) (hb : 0 < b) (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (x : ℕ) (hx : x < n) (i : Fin n) (hi : i.val < x) :
    demandNoPurchaseOv μ b v v0 x / demandOv μ b v v0 x i =
      (AssortSearch.HeurEq.shareNoPurchase v v0 x +
          ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j *
            AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
              (popularSet n x)) /
        (share v v0 (popularSet n x) i *
          (1 - AssortSearch.Cannibal.H μ (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) v v0
            (popularSet n x))) := by sorry

end AssortSearch.MNLQC.Supplement
