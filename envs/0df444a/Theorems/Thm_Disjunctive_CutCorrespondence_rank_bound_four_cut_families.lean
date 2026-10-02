-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_rank_bound_four_cut_families
-- name    : Disjunctive.CutCorrespondence.rank_bound_four_cut_families
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:49:27.338263+00:00
-- url     : https://prove2.me/theorems/bb48936a-63c0-41a7-a87c-e09a75497fa2
-- title:
--   Theorem 8.7 — a uniform rank bound across four cut families
-- statement:
--   This is Theorem 8.7 of Balas's *Disjunctive Programming*, the goal theorem of this
--   mission and the chapter's capstone: the rank of the LP relaxation `P` with respect to each of four
--   cut families — (a) unstrengthened lift-and-project cuts, (b) simple disjunctive cuts, (c)
--   strengthened lift-and-project cuts, (d) mixed integer Gomory cuts (equivalently, strengthened
--   simple disjunctive cuts) — is at most `p`, the number of 0-1 variables.
--
--   The book's proof, for each part, exhibits the *same* recursion `P_0:=P`, `P_j:=conv(P_{j-1}∩
--   {x_j∈{0,1}})` for `j=1,…,p` (reaching `P_p=P^D`, the integer hull, by the sequential
--   convexifiability of facial disjunctive programs): (a) each step is literally an unstrengthened
--   lift-and-project cut closure; (b) by Theorems 8.4A/8.4B, each step's lift-and-project cuts equal
--   some simple disjunctive cuts, so the *same* recursion can be restated in terms of family (b); (c)
--   using strengthened cuts at each step instead gives `P̃_j⊆P_j`, so the same recursion still reaches
--   `P^D`; (d) by Theorem 8.5, each strengthened lift-and-project cut equals a mixed integer Gomory
--   cut, so (c)'s procedure restates in terms of family (d).
--
--   **Formalization Note.** All four parts are stated via one generic `HasRankAtMost` predicate
--   applied to the four cut-closure operators of `Def_..._Rank`, mirroring how the book's own proof
--   reuses one recursion across all four parts rather than four independent arguments.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 105, Theorem 8.7

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau
import Definitions.Def_Disjunctive_CutCorrespondence_Rank

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.7 (Balas §8.4, p. 105), the goal theorem of this mission: the rank of `P` (the LP
relaxation) with respect to each of (a) unstrengthened lift-and-project cuts, (b) simple
disjunctive cuts, (c) strengthened lift-and-project cuts, and (d) mixed integer Gomory cuts
(equivalently, strengthened simple disjunctive cuts) is at most `p := |N'|`, the number of 0-1
variables. Parts (b)-(d) read the cuts off the simplex tableau of `Ã`, so the bound rows
`0 ≤ x_j ≤ 1`, `j ∈ N'`, must be part of the system: for `P = [-1,2]` in one variable with
`N' = {0}` no basis has `0 < ā_{k0} < 1`, the simple disjunctive closure is `P` itself, and
`conv(K₀) = [0,1]` is strictly smaller. -/
theorem rank_bound_four_cut_families {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n))
    (hbounds : Poly A b ⊆ {x | ∀ j ∈ Nprime, 0 ≤ x j ∧ x j ≤ 1}) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card := by sorry

end Disjunctive.CutCorrespondence
