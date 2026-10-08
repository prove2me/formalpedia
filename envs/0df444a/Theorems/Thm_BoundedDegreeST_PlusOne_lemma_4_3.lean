-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_lemma_4_3
-- name    : BoundedDegreeST.PlusOne.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:05.770919+00:00
-- url     : https://prove2.me/theorems/fbd33052-7557-4054-9e32-ce33ad012d41
-- title:
--   Lemma 4.3 — laminar basis for a basic LP solution
-- statement:
--   Let $x^*$ be a basic feasible solution of LP-MBDCT on a well-formed graph and forest before the terminal step, and let $E^*$ be its support. There are a nonempty laminar family $\mathcal L$ of nonempty unions of forest components and a set $T\subseteq W$ such that the tight equations
--
--   $$
--   x^*(E(S))=|S|-|F(S)|-1\quad(S\in\mathcal L),\qquad x^*(\delta(v))=B_v\quad(v\in T)
--   $$
--
--   uniquely determine $x^*$ on $E^*$. Their characteristic vectors are linearly independent and $|E^*|=|\mathcal L|+|T|$.
--
--   This identifies the tight rows used by the token-counting argument.
--
--   **Formalization Note** The linear system, uniqueness and independence are all on the support variables. The nonterminal condition excludes the zero-variable terminal LP.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 666, Lemma 4.3

import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Lemma 4.3, p. 666. -/
theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V]
    (I : Instance V) (x : Sym2 V → ℝ)
    (hvalid : Valid I) (hbasic : Basic I.E I.B I.W I.F x)
    (hnotree : ¬ IsSpanningTree I.F) :
    ∃ (L : Finset (Finset V)) (T : Finset V),
      DefinesBasis I.E I.B I.W I.F x L T := by sorry
end BoundedDegreeST.PlusOne
