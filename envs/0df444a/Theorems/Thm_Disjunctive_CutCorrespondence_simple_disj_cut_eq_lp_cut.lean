-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_simple_disj_cut_eq_lp_cut
-- name    : Disjunctive.CutCorrespondence.simple_disj_cut_eq_lp_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:48:21.579988+00:00
-- url     : https://prove2.me/theorems/6dc6be1c-5025-438c-9708-1f791a33e321
-- title:
--   Theorem 8.4B — the converse: every simple disjunctive cut is a basic lift-and-project cut
-- statement:
--   This is Theorem 8.4B of Balas's *Disjunctive Programming* — **entirely missing from
--   `statements.jsonl`** (only 8.4A was captured, mislabeled "8.4"); verified directly against the PDF
--   and added manually. The book calls it explicitly "Theorem 8.4A's... converse."
--
--   Given any nonsingular `n×n` submatrix `Â` of `Ã` with `0<ā_k0<1`, and the partition `(M1,M2)` of
--   its row set assigning `j` to `M1` when `π¹_j<π²_j` (i.e. `ā_kj<0`) and to `M2` when `π¹_j>π²_j`
--   (i.e. `ā_kj>0`), there is a basic feasible solution to `(CGLP)_k` with `u0,v0>0` and basic
--   components indexed by exactly `(M1,M2)`, whose lift-and-project cut is equivalent to the simple
--   disjunctive cut from `Â`. The book's proof shows the chosen basis is well-defined (since `Â`
--   nonsingular makes (8.3), hence (8.2), have a unique solution) and that this unique solution is
--   exactly (8.9)'s construction — hence feasible.
--
--   **Formalization Note.** Kept as a *separate* item from Theorem 8.4A, per `BRIEF.md`'s explicit
--   warning that their hypotheses differ (8.4B additionally requires `0<ā_k0<1`, which 8.4A gets for
--   free from `u0,v0>0` via Lemma 8.3) — not bundled into one iff statement.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 102, Theorem 8.4B

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.4B (Balas §8.1, p. 101-102), the converse of Theorem 8.4A: given any nonsingular
`n×n` submatrix `Â` of `Ã` (enumerated by `ι`) with `0 < ā_k0 < 1`, and a partition `(M1,M2)` of
its row set assigning `ι i` to `M1` when `π¹_i < π²_i` and to `M2` when `π¹_i > π²_i`, there is a
basic feasible solution to `(CGLP)_k` with `u0,v0>0` and basic `u`/`v` components indexed by
`M1`/`M2`, whose lift-and-project cut `αx ≥ β` is equivalent to the simple disjunctive cut from
`Â`. -/
theorem simple_disj_cut_eq_lp_cut {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (ι : Fin n → M) (hι_inj : Function.Injective ι) (hnonsing : IsUnit (Ahat Atil ι).det)
    (h0 : 0 < Abar0 Atil btil ι k) (h1 : Abar0 Atil btil ι k < 1) (M1 M2 : Finset M)
    (hpart : ∀ i, (Pi1 Atil btil ι k i < Pi2 Atil btil ι k i → ι i ∈ M1) ∧
      (Pi1 Atil btil ι k i > Pi2 Atil btil ι k i → ι i ∈ M2)) :
    ∃ α u u0 v v0 β, IsCGLPKFeasible Atil btil k α u u0 v v0 β ∧ 0 < u0 ∧ 0 < v0 ∧
      (∀ ρ ∉ M1, u ρ = 0) ∧ (∀ ρ ∉ M2, v ρ = 0) ∧
      {x | β ≤ dotProduct α x} = SimpleDisjCutSet Atil btil ι k := by sorry

end Disjunctive.CutCorrespondence
