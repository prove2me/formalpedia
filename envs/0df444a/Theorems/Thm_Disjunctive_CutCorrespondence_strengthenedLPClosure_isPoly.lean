-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_strengthenedLPClosure_isPoly
-- name    : Disjunctive.CutCorrespondence.strengthenedLPClosure_isPoly
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T06:42:24.871836+00:00
-- url     : https://prove2.me/theorems/1f457589-d01a-435e-9b19-d076d17a0c59
-- title:
--   The elementary strengthened lift-and-project closure of a mixed 0-1 polyhedron is a polyhedron
-- statement:
--   Let $P=\{x\in\mathbb R^n:\tilde Ax\ge\tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 variables $N'\subseteq\{1,\dots,n\}$, where, as throughout Chapter 8, the system $\tilde Ax\ge\tilde b$ contains the rows $x_j\ge 0$ for every $j$ and $-x_j\ge -1$ for every $j\in N'$. Fix $k\in N'$.
--
--   For a finite system $A'x\ge b'$ with $\{x:A'x\ge b'\}=P$, consider every feasible solution $(\alpha,\beta,u,u_0,v,v_0)$ of the cut-generating LP $(CGLP)_k$ (eq. (8.1)) of that system with $u_0,v_0>0$, and the strengthened lift-and-project cut $\gamma x\ge\beta$ of Theorem 6.4. For $j\in N'$ the coefficient is
--   $$\gamma_j=\min\{\alpha^1_j+u_0\lceil m_j\rceil,\ \alpha^2_j-v_0\lfloor m_j\rfloor\},\qquad m_j=\frac{\alpha^2_j-\alpha^1_j}{u_0+v_0},$$
--   where $\alpha^1_j,\alpha^2_j$ are $u\tilde A_j, v\tilde A_j$ with the multipliers of the rows $x_j\ge 0$ removed. For $j\notin N'$, $\gamma_j=\alpha_j$. The **strengthened lift-and-project closure** of $P$ for the disjunction $x_k\le 0\ \lor\ x_k\ge 1$ is the intersection, over all such systems $A'x\ge b'$, of $P$ with all these cuts.
--
--   **Claim.** This closure is again a polyhedron: there is a finite system $A''x\ge b''$ with
--   $$\{x: A''x\ge b''\}=\bigcap_{A'x\ge b'\ \text{describing}\ P}\Big(P\cap\bigcap_{(CGLP)_k\text{-feasible},\,u_0,v_0>0}\{x:\gamma x\ge\beta\}\Big).$$
--
--   This is the polyhedrality property that Theorem 8.7(c) uses implicitly. The rank of $P$ with respect to strengthened lift-and-project cuts is defined by applying the elementary closure again to the polyhedron produced by the previous round, which presupposes that this closure is a polyhedron. It is a split-closure-type polyhedrality statement, analogous to the Cook–Kannan–Schrijver theorem.
--
--   **Formalization Note.** `StrengthenedLPClosureOfSet` intersects over every representation `Poly A' b' = S`. If `S` admits no such representation, the intersection is empty and the closure is `Set.univ`. This lemma is therefore exactly what keeps the next round of the iteration in `HasRankAtMost` non-vacuous. Together with the companion lemma for mixed integer Gomory cuts, it is the only ingredient of the mission's goal theorem not proved directly.
-- source:
--   Implicit in Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §8.4, pp. 104-105 (definition of rank w.r.t. a cut generating procedure and proof of Theorem 8.7(c),(d)); cut definitions: Theorem 6.4 and eq. (8.10), p. 103

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Basic
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Rank_v2

namespace Disjunctive.CutCorrespondence

/-- Polyhedrality of the elementary strengthened lift-and-project closure (implicit in the proof of Balas, Theorem 8.7(c), §8.4, p. 105): for the LP relaxation `P = {x : Ax ≥ b}` of a mixed 0-1 program (`IsMixedZeroOneSystem`) and `k ∈ N'`, the closure `StrengthenedLPClosureOfSet P k N'` is again of the form `Poly A' b'`. -/
theorem strengthenedLPClosure_isPoly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hsys : IsMixedZeroOneSystem A b Nprime) (k : Fin n)
    (hk : k ∈ Nprime) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      Poly A' b' = StrengthenedLPClosureOfSet (Poly A b) k Nprime := by sorry

end Disjunctive.CutCorrespondence
