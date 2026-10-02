-- Prove2me | Theorems.Thm_Disjunctive_SimplexTableau_split_disjunction_reduction
-- name    : Disjunctive.SimplexTableau.split_disjunction_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:52:55.286341+00:00
-- url     : https://prove2.me/theorems/d6646c4a-dc5a-4b99-9fe3-0dc4ea4609fb
-- title:
--   Proposition 9.4 — reducing a split disjunction to y ≤ 0 ∨ y ≥ 1
-- statement:
--   This is Proposition 9.4 of Balas's *Disjunctive Programming*, a bridge result to
--   the split-disjunction material of Chapters 10-11 (kept as a milestone here since its own proof
--   uses only this chapter's and Chapter 6's apparatus, even though its main use lies later):
--
--   $$
--   \pi x \le \pi_0 \lor \pi x \ge \pi_0+1 \iff y \le 0 \lor y \ge 1,\ \text{with } y :=
--   \pi x - \pi_0
--   $$
--
--   applied to an instance (MIP) amended with the constraint `y=πx-π0`. The book's own proof is one
--   word: "Obvious" — the equivalence is a direct substitution, not requiring any of the chapter's
--   tableau machinery.
--
--   **Formalization Note.** `π` is kept as an integer vector and `π0` an integer, matching the book's
--   own "split disjunction" definition (`π` integer in the space of integer-constrained variables),
--   though the set equality itself would hold for any reals; cast to `ℝ` via `Int.cast` for the dot
--   product against `x : Fin n → ℝ`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 118, Proposition 9.4

import Mathlib

namespace Disjunctive.SimplexTableau

/-- Proposition 9.4 (Balas §9.4, p. 118): a general split disjunction `πx ≤ π0 ∨ πx ≥ π0+1`
applied to an instance `(MIP)` is equivalent to the disjunction `y ≤ 0 ∨ y ≥ 1` applied to
`(MIP)` amended with the constraint `y = πx - π0`. -/
theorem split_disjunction_reduction {n : ℕ} (MIP : Set (Fin n → ℝ)) (pi : Fin n → ℤ)
    (pi0 : ℤ) :
    {x ∈ MIP | dotProduct (fun j => (pi j : ℝ)) x ≤ (pi0 : ℝ) ∨
        (pi0 : ℝ) + 1 ≤ dotProduct (fun j => (pi j : ℝ)) x} =
      {x | ∃ y : ℝ, x ∈ MIP ∧ y = dotProduct (fun j => (pi j : ℝ)) x - (pi0 : ℝ) ∧
        (y ≤ 0 ∨ 1 ≤ y)} := by sorry

end Disjunctive.SimplexTableau
