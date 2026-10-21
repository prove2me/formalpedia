-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_lemma_1_ii
-- name    : BundleSearch.MatureNew.lemma_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:15.511757+00:00
-- url     : https://prove2.me/theorems/8ad0f9cc-a573-4f6b-b7c9-7a6be16aaebe
-- title:
--   Lemma 1 (ii), p. 9 — three new-product search bands
-- statement:
--   Let a new product be posted at price $p\ge0$, with search cost $0\le c\le1/8$. The purchase and search decisions fall into three bands:
--
--   $$\begin{array}{ll}
--   p\le\sqrt{2c}:&\text{all customers buy without search};\\
--   \sqrt{2c}<p\le1-\sqrt{2c}:&\text{all search and buy exactly when }V_2\ge p;\\
--   1-\sqrt{2c}<p:&\text{none searches or buys}.
--   \end{array}$$
--
--   The band endpoints follow the paper's no-search tie rule. In the search band, demand is $\Pr(V_2\ge p)$; in the first and third bands it is respectively $1$ and $0$. This lemma describes the customer choices that underlie Proposition 1.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 9, Lemma 1(ii)

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Lemma 1(ii), p. 9: the three price bands for a new product when search is affordable. -/
theorem lemma_1_ii (c p : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1 / 8) (hp : 0 ≤ p) :
    (p ≤ Real.sqrt (2 * c) →
      BuysWithoutSearch (nsPayoffNew p) (searchPayoffNew c p) ∧ demandNew c p = 1) ∧
    (Real.sqrt (2 * c) < p → p ≤ 1 - Real.sqrt (2 * c) →
      SearchesNew c p ∧ demandNew c p = probGe p) ∧
    (1 - Real.sqrt (2 * c) < p →
      ¬ BuysWithoutSearch (nsPayoffNew p) (searchPayoffNew c p) ∧
      ¬ SearchesNew c p ∧ demandNew c p = 0) := by sorry

end BundleSearch.MatureNew
