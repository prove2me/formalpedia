-- Prove2me | Theorems.Thm_Disjunctive_SequentialConvex_sequential_convexification_facial
-- name    : Disjunctive.SequentialConvex.sequential_convexification_facial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:25:49.260632+00:00
-- url     : https://prove2.me/theorems/3f9c9c8e-d0bd-428e-ad1f-d03daca56cce
-- title:
--   Theorem 3.1 — faciality is sufficient for sequential convexifiability
-- statement:
--   This is Theorem 3.1 of Balas's *Disjunctive Programming*, the goal theorem of this mission:
--   faciality is sufficient for a disjunctive program's convex hull to be computable one
--   disjunction at a time.
--
--   Let $F$ be the constraint set of a disjunctive program with base polyhedron $F_0$ and
--   disjunctions $(D_j)_{j \in S}$ as above. For an arbitrary ordering $\sigma$ of $S$, define the
--   recursion $F_0, F_1, \dots, F_{|S|}$ as in the companion definition. If the program is
--   **facial** — every inequality appearing in a disjunction defines a face of $F_0$ — then
--
--   $$
--   F_{|S|} = \mathrm{conv}(F),
--   $$
--
--   **regardless of which ordering $\sigma$ of $S$ was used.** This means the convex hull of a
--   facial disjunctive set can be generated in $|S|$ manageable stages, each requiring only the
--   convex hull of a *single* elementary disjunction — a dramatically easier computation than
--   generating $\mathrm{conv}(F)$ directly. The class of facial disjunctive programs includes
--   (pure or mixed) 0-1 programming, nonconvex quadratic programming, separable programming, and
--   the linear complementarity problem, but not general (pure or mixed) integer programming — for
--   which, as the book's Example 1 shows explicitly, sequential convexification can fail.
--
--   **Formalization Note.** The universal quantification over `σ` in the theorem's own hypotheses
--   (rather than fixing one ordering) is what encodes "for an arbitrary ordering" — the theorem
--   asserts the conclusion for every choice of `σ`, matching the book's emphasis that the final
--   result does not depend on the order in which disjunctions are imposed.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 42, Theorem 3.1

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic
import Definitions.Def_Disjunctive_SequentialConvex_Fseq

namespace Disjunctive.SequentialConvex

/-- Theorem 3.1 (Balas §3.1, p. 42): if the disjunctive program `DP` is facial, then the
recursive sequential-convexification construction, applied in any order of `S`, terminates at
`conv F`. -/
theorem sequential_convexification_facial {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ)
    (σ : Fin (Fintype.card S) ≃ S) (hFacial : Facial A b Qidx d d0) :
    Fseq Qidx (F0Set A b) d d0 σ (Fintype.card S) =
      convexHull ℝ (DisjunctiveConstraintSet A b Qidx d d0) := by sorry

end Disjunctive.SequentialConvex
