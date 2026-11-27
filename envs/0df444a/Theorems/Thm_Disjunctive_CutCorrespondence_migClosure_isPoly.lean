-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_migClosure_isPoly
-- name    : Disjunctive.CutCorrespondence.migClosure_isPoly
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T06:42:37.90687+00:00
-- url     : https://prove2.me/theorems/b91126e1-aa09-49e8-a8fa-c45fce0ededa
-- title:
--   The elementary mixed integer Gomory closure of a mixed 0-1 polyhedron is a polyhedron
-- statement:
--   Let $P=\{x\in\mathbb R^n:\tilde Ax\ge\tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 variables $N'\subseteq\{1,\dots,n\}$, where, as throughout Chapter 8, the system $\tilde Ax\ge\tilde b$ contains the rows $x_j\ge 0$ for every $j$ and $-x_j\ge -1$ for every $j\in N'$. Fix $k\in N'$.
--
--   For a finite system $A'x\ge b'$ with $\{x:A'x\ge b'\}=P$, a nonsingular $n\times n$ row-submatrix $\hat A$ of $A'$ (rows $J$), and $0<\bar a_{k0}:=e_k\hat A^{-1}\hat b<1$, the **mixed integer Gomory cut** (strengthened simple disjunctive cut, eq. (8.10)) is
--   $$\sum_{j\in J}\bar\pi_j s_j\ \ge\ \bar a_{k0}(1-\bar a_{k0}),$$
--   where $s_j=(A'x-b')_j$ is the surplus of row $j$. For rows $j$ that are bounds $x_i\ge 0$ of a 0-1 variable $i\in N'$, $\bar\pi_j=\min\{f_{kj}(1-\bar a_{k0}),(1-f_{kj})\bar a_{k0}\}$, with $f_{kj}$ the fractional part of $\bar a_{kj}$. For all other rows, $\bar\pi_j=\max\{\bar a_{kj}(1-\bar a_{k0}),-\bar a_{kj}\bar a_{k0}\}$. The **mixed integer Gomory closure** of $P$ for the disjunction on $x_k$ is the intersection, over all such systems describing $P$, of $P$ with all of these cuts.
--
--   **Claim.** This closure is again a polyhedron: it equals $\{x:A''x\ge b''\}$ for some finite system $A''x\ge b''$.
--
--   This is the polyhedrality property that Theorem 8.7(d) uses implicitly. The MIG rank of $P$ is defined by applying the elementary closure again to the polyhedron produced by the previous round, which presupposes that this closure is a polyhedron. It is a split-closure-type polyhedrality statement, analogous to the Cook–Kannan–Schrijver theorem.
--
--   **Formalization Note.** `MIGClosureOfSet` intersects over every representation `Poly A' b' = S`. If `S` admits no such representation, the intersection is empty and the closure is `Set.univ`. This lemma is therefore exactly what keeps the next round of the iteration in `HasRankAtMost` non-vacuous. Together with the companion lemma for strengthened lift-and-project cuts, it is the only ingredient of the mission's goal theorem not proved directly.
-- source:
--   Implicit in Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.4, pp. 104-105 (definition of rank w.r.t. a cut generating procedure and proof of Theorem 8.7(c),(d)); cut definitions: Theorem 6.4 and eq. (8.10), p. 103

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Rank_v2

namespace Disjunctive.CutCorrespondence

/-- Polyhedrality of the elementary mixed-integer-Gomory closure (implicit in the proof of Balas, Theorem 8.7(d), §8.4, p. 105): for the LP relaxation `P = {x : Ax ≥ b}` of a mixed 0-1 program (`IsMixedZeroOneSystem`) and `k ∈ N'`, the closure `MIGClosureOfSet P k N'` is again of the form `Poly A' b'`. -/
theorem migClosure_isPoly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) (k : Fin n)
    (hk : k ∈ Nprime) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      Poly A' b' = MIGClosureOfSet (Poly A b) k Nprime := by sorry

end Disjunctive.CutCorrespondence
