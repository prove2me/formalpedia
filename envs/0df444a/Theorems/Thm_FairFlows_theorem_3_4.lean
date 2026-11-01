-- Prove2me | Theorems.Thm_FairFlows_theorem_3_4
-- name    : FairFlows.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:54.773044+00:00
-- url     : https://prove2.me/theorems/373592c8-bf35-4756-9025-41e3ea28d3cd
-- title:
--   Theorem 3.4 (corrected: X is assumed to cover p) — optimality criteria via a chain
-- statement:
--   Let the digraph $D_L=(V,L)$ cover a fully supermodular function $p:2^V\to\mathbb Z\cup\{-\infty\}$. There is a chain $\mathcal C^*$ of subsets $V_1\supset V_2\supset\cdots\supset V_q$ of $V$ with $p(V_i)>-\infty$ such that a subset $X\subseteq L$ covering $p$ is a minimum cardinality subset of edges covering $p$ if and only if the following three optimality criteria hold:
--
--   1. (A) $\varrho_X(V_i)=p(V_i)$ for every $V_i$;
--   2. (B) every edge in $X$ enters at least one $V_i$;
--   3. (C) every edge in $L-X$ enters at most one $V_i$.
--
--   These are the complementary slackness conditions of (3.2)–(3.3); through Lemma 4.2 they become the flow criteria (O1)–(O5) of Theorem 4.6.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: a digraph D_L = (V, L) → an edge subset L of a digraph D (D_L is D with L = all edges); reason: Lean convention; same instances
--   - encoding: a chain V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q → a Finset of distinct subsets totally ordered by ⊆ (IsChain); "enters exactly one / at least two" counts members; reason: Lean convention; same instances
--   - correction: a subset X ⊆ L is a minimum cover iff (A), (B), (C) → a subset X ⊆ L that covers p is a minimum cover iff (A), (B), (C); reason: as printed it is false: V = {0,1,2}, L = two copies each of 1→2 and 0→2, p({2}) = 2, p({1,2}) = 1, p(V) = −1, p = −∞ elsewhere (fully supermodular, covered by L); any chain admitting all minimum covers accepts the two 1→2 edges, which do not cover {1,2} (exhaustive check); the proof's complementary slackness presumes a feasible X
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 3.4, p.9

import Mathlib
import Definitions.Def_FairFlows_Covering

set_option autoImplicit false

namespace FairFlows

/-- Theorem 3.4 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.9), corrected. Let `D_L = (V, L)` cover a fully supermodular
function `p`. There is a chain `C* = {V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q}` with `p(Vᵢ) > −∞` such that a subset
`X ⊆ L` covering `p` is a minimum cardinality subset of edges covering `p` if and only if
(A) `ϱ_X(Vᵢ) = p(Vᵢ)` for every `Vᵢ`; (B) every edge in `X` enters at least one `Vᵢ`; (C) every
edge in `L − X` enters at most one `Vᵢ`.

**Formalization Note** The criteria are complementary slackness conditions and characterize
minimality among covers only. As printed, for every `X ⊆ L`, the statement is false: on
`V = {0,1,2}` with `L` two copies each of `1→2` and `0→2`, `p({2}) = 2`, `p({1,2}) = 1`,
`p(V) = −1` and `p = −∞` elsewhere (fully supermodular, covered by `L`), every chain that
characterizes the minimum covers among covers also accepts the two `1→2` edges, which do not
cover `{1,2}`. The hypothesis "`X` covers `p`" is therefore added. -/
theorem theorem_3_4 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ)
    (hp : IsSupermodular p) (hcov : Covers D L p) :
    ∃ C : Finset (Finset V), IsChain (· ⊆ ·) (C : Set (Finset V)) ∧ (∀ Z ∈ C, p Z ≠ ⊥) ∧
      ∀ X : Finset A, X ⊆ L → Covers D X p →
        (IsMinCover D L X p ↔
          ((∀ Z ∈ C, ((inDeg D X Z : ℤ) : WithBot ℤ) = p Z) ∧
           (∀ e ∈ X, ∃ Z ∈ C, D.Enters e Z) ∧
           (∀ e ∈ L, e ∉ X → enterCount D C e ≤ 1))) := by sorry

end FairFlows
