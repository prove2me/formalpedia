-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_no_purchase_ratio
-- name    : AssortSearch.HeurEq.no_purchase_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:03.579983+00:00
-- url     : https://prove2.me/theorems/026eb0c8-36c5-44e1-a627-2ac61226c280
-- title:
--   The no-purchase ratio $q_0^{si}(x)/q_i^{si}(x)$ in the independent assortment model
-- statement:
--   In the independent assortment search model with $v_1,\dots,v_n>0$, $v_0>0$, $\lambda>0$ and the assortment $\{1,\dots,x\}$, write $q_j^m(x)=v_j/(v_0+\sum_{k\le x}v_k)$ and $q_0^m(x)=v_0/(v_0+\sum_{k\le x}v_k)$ for the no-search shares, $H(\bar U,x)=\exp(-\lambda(v_0+\sum_{k\le x}v_k))$ for the search probability, and $q_0^{si}(x)=1-\sum_{j\le x}q_j^{si}(x)$ for the no-purchase demand. For every product variant $i$ in the assortment,
--   $$\frac{q_0^{si}(x)}{q_i^{si}(x)}=\frac{q_0^m(x)+\sum_{j\le x}q_j^m(x)\,H(\bar U,x)}{q_i^m(x)\big(1-H(\bar U,x)\big)}.$$
--
--   The right-hand side depends on the assortment: the relative preference of the no-purchase option to a product variant is not independent of the assortment, so IIA fails with respect to the no-purchase option.
--
--   **Formalization Note** $q_0^{si}(x)$ is the normalised no-purchase demand $d_0(x)$ of (14); $\lambda>0$ is a free parameter.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 21 (PDF 23), §5.1, display for q_0^si(x)/q_i^si(x)

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- The relative preference of the no-purchase variant in the independent assortment model
(p. 21): for a product variant `i` of the assortment `x`,
`q_0^si(x) / q_i^si(x) = (q_0^m(x) + ∑_{j ≤ x} q_j^m(x) H(Ū, x)) / (q_i^m(x) (1 − H(Ū, x)))`. -/
theorem no_purchase_ratio {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (i : Fin n) (hi : i.val < x) :
    demandNoPurchase lam v v0 x / demand lam v v0 x i =
      (shareNoPurchase v v0 x +
          ∑ j ∈ popularSet n x, share v v0 (popularSet n x) j * searchH lam v v0 x) /
        (share v v0 (popularSet n x) i * (1 - searchH lam v v0 x)) := by sorry

end AssortSearch.HeurEq
