-- Prove2me | Theorems.Thm_AppliedComb_InclExcl_inclusion_exclusion
-- name    : AppliedComb.InclExcl.inclusion_exclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:58.109759+00:00
-- url     : https://prove2.me/theorems/5af4e5e0-8314-4e50-acbc-7190f0b0ee3d
-- title:
--   Theorem 7.7 — Principle of Inclusion-Exclusion
-- statement:
--   Let $X$ be a finite set and $\mathcal P = \{P_1, \dots, P_m\}$ a family of properties of the elements of $X$. For $S \subseteq [m]$ let $N(S)$ be the number of elements of $X$ that satisfy $P_i$ for every $i \in S$. Then the number of elements of $X$ which satisfy none of the properties in $\mathcal P$ is
--   $$\bigl|\{x \in X : x \text{ satisfies no } P_i\}\bigr| = \sum_{S \subseteq [m]} (-1)^{|S|} N(S). \qquad (7.2.1)$$
--
--   This is the counting principle of the chapter: the enumeration of surjections (Theorem 7.9) and of derangements (Theorem 7.11) are obtained from it by computing $N(S)$ for particular families of properties.
--
--   **Formalization Note.** Properties are a decidable predicate family `P : Fin m → X → Prop` on a `Fintype X`, and $N(S)$ is `AppliedComb.InclExcl.N P S`; the sum ranges over all `S : Finset (Fin m)`. The identity is stated in $\mathbb Z$ because the alternating sum is not a natural-number expression term by term. The statement holds for every $m \ge 0$ (the book's induction starts at $m = 1$; for $m = 0$ both sides equal $|X|$). This is the book's "none of the properties" form, not the cardinality-of-a-union form.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 145, Theorem 7.7

import Mathlib
import Definitions.Def_AppliedComb_InclExcl_N

namespace AppliedComb.InclExcl

/-- Theorem 7.7 (Principle of Inclusion-Exclusion), Keller & Trotter p. 145: for a finite set
`X` and a family of properties `P_1, …, P_m` (indexed by `Fin m`), the number of elements of
`X` which satisfy none of the properties is `∑_{S ⊆ [m]} (-1)^{|S|} N(S)` (Eq. (7.2.1)). -/
theorem inclusion_exclusion {X : Type*} [Fintype X] (m : ℕ) (P : Fin m → X → Prop)
    [∀ i, DecidablePred (P i)] :
    ((Finset.univ.filter (fun x : X => ∀ i : Fin m, ¬ P i x)).card : ℤ) =
      ∑ S : Finset (Fin m), (-1 : ℤ) ^ S.card * (N P S : ℤ) := by sorry

end AppliedComb.InclExcl
