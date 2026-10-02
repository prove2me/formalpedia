-- Prove2me | Theorems.Thm_Disjunctive_Dominants_single_inequality_dominant_facets
-- name    : Disjunctive.Dominants.single_inequality_dominant_facets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:09:36.750322+00:00
-- url     : https://prove2.me/theorems/75fe8be1-adc8-470c-b887-c309a5c772e6
-- title:
--   Theorem 13.3 — the dominant of a single-inequality upper monotone polytope
-- statement:
--   This is Theorem 13.3 of Balas's *Disjunctive Programming*: an explicit, exponentially-large
--   but fully described facet system for the dominant of a single-inequality upper monotone
--   polytope, the direct predecessor to Theorem 13.7's general characterization.
--
--   Let $P = \{x\in[0,1]^n : ax\ge1\}$ ($a\ge0$) be upper monotone. Then
--   $$
--   P^+ = \Big\{x \ge 0 : \sum_{j\in S} \frac{a_j x_j}{1-a(N\setminus S)} \ge 1 \ \text{ for every }
--   S\subseteq N \text{ with } 1-a(N\setminus S) > 0\Big\}.
--   $$
--
--   The book's proof derives validity by combining, for each $S$, the constraints $z_j\ge x_j$
--   (weighted by $a_j$, $j\in S$), $ax\ge1$ (weight $1$), and $-x_j\ge-1$ (weighted by $a_j$,
--   $j\notin S$); the converse direction constructs an explicit witness $x^*$ (equal to $z$ on
--   $S:=\{j : z_j<1\}$ and $1$ elsewhere) and verifies it lies in $P$.
--
--   **Formalization Note.** `SumOver a (Finset.univ \ S)` is `a(N\setminus S)`; the hypothesis
--   `0 < 1 - SumOver a (Finset.univ \ S)` matches the printed side condition "such that
--   $1-a(N\setminus S)>0$" exactly, restricting the quantifier to the subsets $S$ for which the
--   displayed inequality is even well-formed (nonzero denominator).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 218, Theorem 13.3

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Theorem 13.3 (Balas §13.1, p. 218): for `P = {x∈[0,1]ⁿ : ax≥1}` (`a≥0`) upper monotone,
`P⁺ = {x≥0 : Σ_{j∈S} a_jx_j/(1-a(N\S)) ≥ 1 for every S⊆N with 1-a(N\S)>0}`. The page has `1 ∈ P`, i.e. `a(N) ≥ 1`; with `n = 1`, `a = 1/2` the set `P` is empty while the
right-hand side is `[2,∞)`. -/
theorem single_inequality_dominant_facets {n : ℕ} (a : Fin n → ℝ) (ha : 0 ≤ a)
    (P : Set (Fin n → ℝ)) (hP : P = UnitCube n ∩ {x | 1 ≤ dotProduct a x})
    (hupper : IsUpperMonotone P) (haN : 1 ≤ ∑ j, a j) :
    Dominant P = {x | 0 ≤ x ∧ ∀ S : Finset (Fin n), 0 < 1 - SumOver a (Finset.univ \ S) →
      1 ≤ (∑ j ∈ S, a j * x j) / (1 - SumOver a (Finset.univ \ S))} := by sorry

end Disjunctive.Dominants
