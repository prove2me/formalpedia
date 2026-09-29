-- Prove2me | Theorems.Thm_ABC_sum_triples_finite_iff_bddAbove
-- name    : ABC.sum_triples_finite_iff_bddAbove
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:54:41.31287+00:00
-- url     : https://prove2.me/theorems/5e056e65-4eda-485d-a74d-9fe066e15584
-- title:
--   Finiteness of additive triples is equivalent to boundedness of the sum
-- statement:
--   **Finiteness of a family of additive triples is equivalent to boundedness of its largest member.**
--
--   Let $P$ be an arbitrary property of ordered triples of natural numbers and put
--   $$S_P \;=\; \{(a,b,c) \in \mathbb{N}^3 \;:\; a>0,\ b>0,\ a+b=c,\ P(a,b,c)\}.$$
--   Then
--   $$S_P \text{ is finite} \iff \{\, c : (a,b,c) \in S_P \,\} \text{ is bounded above.}$$
--
--   One direction is immediate: the image of a finite set is finite, and a finite set of naturals is bounded above. The other direction is the useful one. The constraint $a+b=c$ with $a,b>0$ forces $a \le c$ and $b \le c$, so a bound $c \le C$ confines the whole triple to the box $[0,C]^3$; the family is then finite as a subset of a finite set. The additive relation is what makes this work — for a general set of triples, bounding one coordinate says nothing about the others.
--
--   The statement is phrased for an arbitrary predicate $P$ so that it can be instantiated at any specific condition. Its intended use is the $abc$ conjecture, whose assertion for a fixed $\varepsilon > 0$ is the finiteness of
--   $$\{(a,b,c) : a,b,c>0,\ a,b,c \text{ pairwise coprime},\ a+b=c,\ \operatorname{rad}(abc)^{1+\varepsilon} < c\},$$
--   a set of exactly this shape. Taking $P$ to be the coprimality-and-radical condition converts that finiteness claim into the equivalent statement that the $c$-values occurring in $abc$-triples of quality $> 1+\varepsilon$ are bounded — the form in which the conjecture is usually quantified, and the form in which explicit numerical searches for extremal triples report their results.
-- source:
--   Elementary reformulation used throughout the abc literature; see e.g. the discussion of quality and of the finiteness formulation in Granville-Tucker, It's As Easy As abc, Notices AMS 49 (2002) 1224-1231, Section 1. Stated here in the ordered-triple shape of the platform statement ABC_Conjecture (following https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ABC.lean), with the extra condition left as an arbitrary predicate P.

import Mathlib

open scoped BigOperators

namespace ABC

theorem sum_triples_finite_iff_bddAbove (P : ℕ × ℕ × ℕ → Prop) :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ P t}.Finite ↔
      BddAbove ((fun t : ℕ × ℕ × ℕ => t.2.2) ''
        {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ P t}) := by sorry

end ABC
