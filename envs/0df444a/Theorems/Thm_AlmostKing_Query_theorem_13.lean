-- Prove2me | Theorems.Thm_AlmostKing_Query_theorem_13
-- name    : AlmostKing.Query.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:11.549658+00:00
-- url     : https://prove2.me/theorems/170933f2-d76c-42db-a97b-9d1cf9349084
-- title:
--   Theorem 13 — small subsets inherit lower-regularity
-- statement:
--   For every $0<\chi<1$, there exist constants $\xi_0,K>0$ independent of all vertex sets, graphs, densities, and sample sizes. Let $X,Y$ be disjoint nonempty finite sets, and let $E$ be a relation whose restriction to $X\times Y$ is $(\xi,q)$-lower-regular, where $0<\xi\le\xi_0$ and $0<q<1$. For every integer $L$ with $K/q\le L\le|X|$,
--   $$|\{A\subseteq X:|A|=L,\ (A,Y)\text{ is }(\chi,q)\text{-lower-regular}\}|\ge(1-2^{-L})\binom{|X|}{L}.$$
--
--   This is the inheritance theorem attributed by the source to Gerke, Kohayakawa, Rödl and Steger, including the full quantitative count of good subsets.
--
--   Differences from the source:
--   - generalization: a bipartite graph on nonempty classes $X\sqcup Y$ → an arbitrary relation on a finite ambient type, restricted to disjoint nonempty $X\times Y$; reason: every such restriction is exactly the incidence relation of a bipartite graph, and outside values are unused
--   - encoding: an integer $L$ satisfying $K/q\le L$ → a natural number $L$ satisfying the same real inequality; reason: positivity of $K$ and $q$ already forces $L>0$
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Theorem 13 ([GKRS07, Theorem 3.6]), p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

open Classical

namespace AlmostKing.Query

/-- Theorem 13, p. 9, attributed there to GKRS07, Theorem 3.6.
Only the restriction of E to X × Y matters, so this includes bipartite graphs. -/
theorem theorem_13 : ∀ χ : ℝ, 0 < χ → χ < 1 →
    ∃ ξ₀ K : ℝ, 0 < ξ₀ ∧ 0 < K ∧
    ∀ (V : Type) [Fintype V] (E : V → V → Prop) (X Y : Finset V),
    ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ q : ℝ, 0 < q → q < 1 →
    IsLowerRegular E ξ q X Y → ∀ L : ℕ, K / q ≤ (L : ℝ) → L ≤ X.card →
      (1 - (2 : ℝ) ^ (-(L : ℝ))) * (X.card.choose L : ℝ) ≤
        (((X.powersetCard L).filter (fun A => IsLowerRegular E χ q A Y)).card : ℝ) := by sorry

end AlmostKing.Query
