-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_iia_independent
-- name    : AssortSearch.HeurEq.iia_independent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:04.169119+00:00
-- url     : https://prove2.me/theorems/b676839b-3095-4131-a583-4fa527e0057a
-- title:
--   IIA between product variants in the independent assortment model: $q_i^{si}(x)/q_j^{si}(x)=v_i/v_j$
-- statement:
--   In the independent assortment search model with preferences $v_1,\dots,v_n>0$, no-purchase preference $v_0>0$ and search constant $\lambda>0$, let $d_i(x)=q_i^{si}(x)$ be the demand of variant $i$ when the assortment is $\{1,\dots,x\}$. For any two product variants $i,j$ in the assortment,
--   $$\frac{q_i^{si}(x)}{q_j^{si}(x)}=\frac{v_i}{v_j}.$$
--
--   Thus the independence of irrelevant alternatives, a classical property of the multinomial logit model, survives consumer search as long as only product variants are compared. It is what lets the retailer recover the relative preferences of product variants from sales data.
--
--   **Formalization Note** Variants are 0-based `Fin n`; "$i$ in the assortment $x$" is `i.val < x`. Only the independent-model line of the page is stated; the overlapping-model line is outside this mission.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 21 (PDF 23), §5.1, the IIA display for q^si

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- IIA among product variants in the independent assortment model (p. 21):
`q_i^si(x) / q_j^si(x) = v_i / v_j` for product variants `i, j` of the assortment `x`. -/
theorem iia_independent {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (i j : Fin n) (hi : i.val < x) (hj : j.val < x) :
    demand lam v v0 x i / demand lam v v0 x j = v i / v j := by sorry

end AssortSearch.HeurEq
