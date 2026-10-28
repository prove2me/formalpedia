-- Prove2me | Theorems.Thm_DisplayMNL_Rounding_revenue_insert
-- name    : DisplayMNL.Rounding.revenue_insert
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:52.419589+00:00
-- url     : https://prove2.me/theorems/bd245223-c734-4c0a-878c-311784355559
-- title:
--   §3.1, p. 13 (proof of Lemma 3.1) — adding one item: R(S ∪ {i}) is a convex combination of R(S) and r_i
-- statement:
--   Let $r_i>0$ and $w_i>0$ be the prices and MNL weights of the items, and $R(S)=\rho(S)/(1+w(S))$ the expected revenue of an assortment $S$, where $\rho(S)=\sum_{i\in S}r_iw_i$ and $w(S)=\sum_{i\in S}w_i$. For every assortment $S$ and every item $i\notin S$,
--   $$R(S\cup\{i\})=R(S)\cdot\frac{1+w(S)}{1+w(S)+w_i}+r_i\cdot\frac{w_i}{1+w(S)+w_i}.$$
--
--   The two coefficients are positive and sum to one, so the revenue after adding an item lies between the previous revenue and the item's price. This is the basic monotonicity tool behind the unimodality of the revenue function along an assignment (Claim 5.5).
--
--   **Formalization Note** The paper speaks of "adding a single item $i$ to $S$"; the hypothesis $i\notin S$ makes this explicit (for $i\in S$ the identity fails).
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), p. 13, §3.1, proof of Lemma 3.1 (unnumbered display); also App. C.7, p. 49

import Mathlib
import Definitions.Def_DisplayMNL_Rounding_Model

open Finset

namespace DisplayMNL.Rounding

theorem revenue_insert {n : ℕ} (I : Instance n) (hr : ∀ i, 0 < I.r i) (hw : ∀ i, 0 < I.w i)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    rev I (insert i S) =
      rev I S * ((1 + wt I S) / (1 + wt I S + I.w i)) + I.r i * (I.w i / (1 + wt I S + I.w i)) := by sorry

end DisplayMNL.Rounding
