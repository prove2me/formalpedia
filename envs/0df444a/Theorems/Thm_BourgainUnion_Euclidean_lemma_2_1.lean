-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_2_1
-- name    : BourgainUnion.Euclidean.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:03.00461+00:00
-- url     : https://prove2.me/theorems/011e519b-214a-4837-b69c-47373964ae61
-- title:
--   Lemma 2.1 — two-sided Kirszbraun collapse
-- statement:
--   There are absolute positive real constants $a,b$ such that, for every finite- or countably-dimensional real Hilbert space $H$ and every nonempty subset $S\subseteq H$, there is a map $\psi:H\to\ell_2$ with $\psi|_S=0$ and
--   $$a\min\{\|x-y\|,R(x)+R(y)\}\le\|\psi(x)-\psi(y)\|\le b\min\{\|x-y\|,R(x)+R(y)\},$$
--   where $R(x)=\operatorname{dist}(x,S)$. The constants precede the dimension, subset and points. Closedness and boundedness are not assumed. This is the paper's cited two-sided collapse input, rather than ordinary Lipschitz extension alone.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: Θ with absolute constants independent of S and dimension → ∃ a b>0, CollapseConstants a b; reason: the quantified predicate spells out both inequalities with one pair of constants across all instances
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 5, Lemma 2.1

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_VoronoiModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 2.1: constants precede every subset and every Hilbert dimension. -/
theorem lemma_2_1 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ CollapseConstants a b := by sorry

end BourgainUnion.Euclidean
