-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_rank_bound_four_cut_families_v2
-- name    : Disjunctive.CutCorrespondence.rank_bound_four_cut_families_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:35.069486+00:00
-- url     : https://prove2.me/theorems/4e2ef06e-08ac-4e04-92b8-bdbc9afa5b41
-- title:
--   Theorem 8.7 — the rank of $P$ w.r.t. L&P, simple disjunctive, strengthened L&P and MIG cuts is at most $p$
-- statement:
--   Let $P=\{x\in\mathbb R^n:\tilde Ax\ge\tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 variables $N'$, where, as throughout Chapter 8, the system $\tilde Ax\ge\tilde b$ contains the rows $x_j\ge 0$ ($j=1,\dots,n$) and $-x_j\ge -1$ ($j\in N'$). Then the rank of $P$ with respect to each of the following cut families is at most $p:=|N'|$:
--
--   (a) unstrengthened lift-and-project cuts;
--   (b) simple disjunctive cuts;
--   (c) strengthened lift-and-project cuts;
--   (d) mixed integer Gomory cuts (strengthened simple disjunctive cuts).
--
--   That is, for each family there is an ordering $j_1,\dots,j_p$ of $N'$ such that applying the family's elementary closure for the disjunctions $x_{j_1}\in\{0,1\},\dots,x_{j_p}\in\{0,1\}$ in turn produces $\operatorname{conv}\{x\in P: x_j\in\{0,1\},\ j\in N'\}$.
--
--   **Formalization Note.** The retired version was refuted through part (d): its `PiBar` applied the Gomory strengthening to the surplus of an arbitrary row (with $N'$ read as a set of row positions), which yields cuts invalid for the integer hull. The corrected definitions strengthen only nonbasic positions whose row is a bound $x_j\ge 0$ with $j\in N'$ ("$j\in J\cap N'$"), and Theorem 6.4's $\gamma$ now omits the multipliers of $x_j\ge 0$ from $u\tilde A_j,v\tilde A_j$ (the retired $\gamma$ equalled $\alpha$). The chapter's standing assumption is stated as the book states it, as rows of the system (`IsMixedZeroOneSystem`), instead of the weaker `Poly A b ⊆ box`. The rank is formalized, as in the retired version, by one generic predicate `HasRankAtMost` over an enumeration of $N'$; closures of the representation-dependent families are intersected over all linear representations of the current polyhedron.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.4, p. 105, Theorem 8.7

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Rank_v2

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.7 (Balas, *Disjunctive Programming*, §8.4, p. 105), the goal theorem of this
mission: for the LP relaxation `P = {x : Ãx ≥ b̃}` of a mixed 0-1 program, the rank of `P` with
respect to each of (a) unstrengthened lift-and-project cuts, (b) simple disjunctive cuts,
(c) strengthened lift-and-project cuts, and (d) mixed integer Gomory cuts (strengthened simple
disjunctive cuts) is at most `p := |N'|`, the number of 0-1 variables.

Corrected from the retired version: the MIG strengthening (`PiBar`) is applied only to nonbasic
positions whose row is the bound `x_j ≥ 0` of a 0-1 variable (the retired `PiBar` strengthened
the surplus of arbitrary rows, producing invalid "cuts"), Theorem 6.4's `Gamma` now removes the
multipliers of `x_j ≥ 0` from `uÃ_j, vÃ_j`, and the standing assumption of the chapter is stated
as the book does: the system `Ãx ≥ b̃` contains the rows `x_j ≥ 0` (all `j`) and `-x_j ≥ -1`
(`j ∈ N'`). -/
theorem rank_bound_four_cut_families_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) :
    HasRankAtMost SplitConvexify (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost SimpleDisjClosureOfSet (Poly A b) Nprime Nprime.card ∧
      HasRankAtMost (fun S k => StrengthenedLPClosureOfSet S k Nprime) (Poly A b) Nprime
        Nprime.card ∧
      HasRankAtMost (fun S k => MIGClosureOfSet S k Nprime) (Poly A b) Nprime Nprime.card := by sorry

end Disjunctive.CutCorrespondence
