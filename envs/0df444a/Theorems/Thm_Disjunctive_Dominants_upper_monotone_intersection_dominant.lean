-- Prove2me | Theorems.Thm_Disjunctive_Dominants_upper_monotone_intersection_dominant
-- name    : Disjunctive.Dominants.upper_monotone_intersection_dominant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:09:09.273511+00:00
-- url     : https://prove2.me/theorems/7eee0ad2-ed93-4527-86d4-9c9b9cf8429b
-- title:
--   Proposition 13.1 — the dominant of an upper monotone intersection
-- statement:
--   This is Proposition 13.1 of Balas's *Disjunctive Programming*: for an upper monotone
--   polytope presented as an intersection of single-inequality pieces, the dominant distributes
--   over the intersection.
--
--   Let $P = \{x\in[0,1]^n : Ax\ge 1\}$ ($A\ge0$) be upper monotone, and write $P = \bigcap_i P_i$
--   with $P_i := \{x\in[0,1]^n : a_ix\ge1\}$ for each row $a_i$ of $A$. Then $P^+ = \bigcap_i
--   P_i^+$.
--
--   The book's proof: if $z \in P^+$, some $x\in P$ has $x\le z$; since $x\in P_i$ for every $i$,
--   $z\in P_i^+$ for every $i$. Conversely, if $z\in\bigcap_i P_i^+$, each $P_i$ contributes a
--   witness $x^i\le z$; the coordinatewise maximum $x^* := \max_i x^i$ lies in $[0,1]^n$, satisfies
--   every row ($a_ix^*\ge a_ix^i\ge1$), hence lies in $P$, and $z\ge x^*$ places $z$ in $P^+$.
--
--   **Formalization Note.** The immediately following remark ("if $P=\bigcap_i P_i$ is *not* upper
--   monotone, then $P^+\subseteq\bigcap_i P_i^+$, but the converse is not always true") is not
--   itself a numbered result and is not drafted as a separate item; it is recorded here as context
--   for why the `hupper` hypothesis cannot be dropped.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 217-218, Proposition 13.1

import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Proposition 13.1 (Balas §13.1, p. 217-218): if `P` is an upper monotone polytope of the form
`P = {x∈[0,1]ⁿ : Ax≥1}` with `A≥0`, i.e. `P = ⋂_i P_i` for `P_i := {x∈[0,1]ⁿ : a_ix≥1}`, then
`P⁺ = ⋂_i P_i⁺`. At `m = 0` the system is empty, `0 ∈ P` against the page's standing `0 ∉ P`, and the empty
intersection is all of `ℝⁿ` while the dominant is `{x ≥ 0}`. -/
theorem upper_monotone_intersection_dominant {n m : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : Set (Fin n → ℝ)) (Pi : Fin m → Set (Fin n → ℝ))
    (hP : P = UnitCube n ∩ {x | ∀ i, 1 ≤ dotProduct (A i) x})
    (hPi : ∀ i, Pi i = UnitCube n ∩ {x | 1 ≤ dotProduct (A i) x})
    (hupper : IsUpperMonotone P) :
    Dominant P = ⋂ i, Dominant (Pi i) := by sorry

end Disjunctive.Dominants
