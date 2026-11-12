-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_online_cover_exists
-- name    : BudgetedAffine.Disjoint.online_cover_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:47.553407+00:00
-- url     : https://prove2.me/theorems/6cd4b832-852f-4b42-af95-49bcf1005a5a
-- title:
--   Online fractional covering is $O(\log n)$-competitive (Buchbinder–Naor), in the form (4.4)
-- statement:
--   Consider the online fractional covering problem
--   $$\min\{d^\top y : My\ge \mathbb 1,\ y\ge 0\}$$
--   with a non-negative constraint matrix $M\in\mathbb R_+^{m\times n}$ and a cost vector $d\in\mathbb R_+^n$. The covering requirements arrive online in batches $S_1,S_2,\dots\subseteq[m]$: when $S_r$ arrives, the algorithm must augment its current solution $y^{\mathcal A}$ (it may never decrease it) so that every revealed row is covered.
--
--   There are constants $K>0$ and $N$ such that for every $n\ge N$, every $m$, every such $M$ and every such $d$, there is an online algorithm with the following properties:
--
--   1. it starts from $y=0$ and only ever augments its non-negative solution;
--   2. whenever the revealed rows can be covered at all, it covers every revealed row;
--   3. for every sequence of pairwise disjoint batches whose union $S_1\cup\dots\cup S_R$ can be covered, its cost satisfies
--   $$\mathcal A(S_1,\dots,S_R)\le K\log n\cdot\Theta\big(\mathbb 1(S_1\cup\dots\cup S_R)\big),$$
--   where $\Theta(h)=\min_{y\ge0}\{d^\top y: My\ge h\}$ is the offline covering cost.
--
--   This is the $O(\log n)$-competitive online fractional covering algorithm of Buchbinder and Naor that El Housni and Goyal use in Section 4.1 (eq. (4.4)) to construct both the greedy scenario of Algorithm 1 and the affine policy for disjoint constrained budgeted sets.
--
--   **Formalization Note** "Online algorithm with competitive ratio $\rho$" is the platform structure `OnlineCover M d ρ` (definition `BudgetedAffine_Disjoint_OnlineCover`). Its solution is a function of the revealed list of batches, which encodes the online (prefix-only) dependence. Variables with zero cost are allowed; $\log$ is the natural logarithm.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. 34(2):270-286, 2009, Theorem 4.1 (O(log n)-competitive online fractional covering); used as eq. (4.4) in El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 4.1, p. 15

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover

namespace BudgetedAffine.Disjoint

open Matrix

/-- Buchbinder–Naor: online fractional covering admits an `O(log n)`-competitive online algorithm,
i.e. there are `K > 0` and `N` such that for every `n ≥ N`, every non-negative `M ∈ ℝ^{m×n}` and
every cost `d ≥ 0` there is an online covering algorithm for `M`, `d` with competitive ratio
`K log n` (in the sense of `OnlineCover`). -/
theorem online_cover_exists :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (m : ℕ) (M : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ),
      (∀ i j, 0 ≤ M i j) → 0 ≤ d → Nonempty (OnlineCover M d (K * Real.log n)) := by sorry

end BudgetedAffine.Disjoint
