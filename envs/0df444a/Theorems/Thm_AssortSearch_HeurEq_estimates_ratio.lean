-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_estimates_ratio
-- name    : AssortSearch.HeurEq.estimates_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:36.017985+00:00
-- url     : https://prove2.me/theorems/2ebfa605-c7da-4b8c-9212-5d606c3c1fd5
-- title:
--   Iterative assortment planning estimates relative preferences correctly: $\hat v_i(x)/\hat v_j(x)=v_i/v_j$
-- statement:
--   Consider the independent assortment search model with preferences $v_1,\dots,v_n>0$, $v_0>0$ and $\lambda>0$. For an assortment of depth $1\le x\le n$ let $\hat v(x)=(\hat v_0(x),\dots,\hat v_x(x),\hat v_{x+1}(n),\dots,\hat v_n(n))$ be the preferences the retailer estimates from the observed demands, normalised by $\hat v_1(x)=1$, with depth-test estimates for the variants not carried. Then for all product variants $0<i<j\le n$,
--   $$\frac{\hat v_i(x)}{\hat v_j(x)}=\frac{v_i}{v_j}.$$
--
--   Given that the preference of variant 1 is held fixed, the iterative procedure therefore estimates every product variant's preference correctly under any assortment; only the no-purchase estimate $\hat v_0(x)$ is biased.
--
--   **Formalization Note** 0-based indices: the paper's $0<i<j\le n$ is `i < j` in `Fin n`. The depth $x$ satisfies $1\le x\le n$, the range where the estimates are defined.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 21 (PDF 23), §5.1, display v̂_i(x)/v̂_j(x) = v_i/v_j

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Iterative assortment planning estimates the relative preferences of the product variants
correctly under any assortment (p. 21): for every depth `1 ≤ x ≤ n` and all variants
`0 < i < j ≤ n` (0-based: `i < j` in `Fin n`), `v̂_i(x) / v̂_j(x) = v_i / v_j`. Variants outside
`x` carry the depth-test estimates `v̂_i(n)`. -/
theorem estimates_ratio {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) (i j : Fin n) (hij : i < j) :
    estPref lam v v0 x i / estPref lam v v0 x j = v i / v j := by sorry

end AssortSearch.HeurEq
