-- Prove2me | Theorems.Thm_BlottoLP_Flow_theorem_4_6
-- name    : BlottoLP.Flow.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:52.474427+00:00
-- url     : https://prove2.me/theorems/bf5278e3-c261-4bff-b654-688239ec0dbb
-- title:
--   Theorem 4.6, p. 8 — 𝒫_A is the projection of a linear system with O(N²K) constraints and O(N²K) variables
-- statement:
--   There is a constant $c$ such that the following holds. In every instance of Colonel Blotto with $K\ge 1$ battlefields and at most $N\ge 1$ troops for each player ($A\le N$, $B\le N$), the set $\mathcal P_A$ of marginals of player A's Nash-equilibrium strategies has a linear formulation with at most $c\,N^2K$ constraints and at most $c\,N^2K$ variables: there is a system of at most $c\,N^2K$ linear equations and inequalities in the coordinates of $\hat x$ and auxiliary variables, with at most $c\,N^2K$ variables in total, such that
--   $$
--   \hat x\in\mathcal P_A\iff \text{the system has a solution extending } \hat x .
--   $$
--
--   Before this result, the only known description of $\mathcal P_A$ (Ahmadinejad et al.) used exponentially many constraints and had to be solved with the ellipsoid method; Theorem 4.6 gives a description of polynomial size that a standard LP solver can handle.
--
--   **Formalization Note** "$\Theta(N^2K)$" is read as the upper bound $O(N^2K)$ with one constant $c$ that is fixed before the instance; the matching lower bound is the paper's Theorem 5.6, which is not part of this mission. Constraints are equations plus inequalities and variables are the coordinates of $\mathcal P_A$ plus the auxiliary ones, as in the paper's count for Linear Program 1. The hypotheses $K\ge1$ and $N\ge1$ are added because $c\,N^2K$ vanishes otherwise while $\mathcal P_A$ may still need a constraint. The platform's `ExtensionComplexity.TSP.IsEFOfSize` counts inequalities only and is not used.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 8, Theorem 4.6 (proof pp. 9–11)

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model
import Definitions.Def_BlottoLP_Flow_LinearFormulation

namespace BlottoLP.Flow

/-- Theorem 4.6: there is a constant `c` such that, in every instance of Colonel Blotto with
`K ≥ 1` battlefields and at most `N ≥ 1` troops for each player, `𝒫_A` has a linear formulation
with at most `c · N² · K` constraints and at most `c · N² · K` variables. -/
theorem theorem_4_6 :
    ∃ c : ℕ, ∀ (I : Instance) (N : ℕ), 1 ≤ I.K → 1 ≤ N → I.A ≤ N → I.B ≤ N →
      HasLinearFormulation (PA I) (c * N ^ 2 * I.K) (c * N ^ 2 * I.K) := by sorry

end BlottoLP.Flow
