-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_greedy_run_exists
-- name    : BudgetedAffine.Disjoint.greedy_run_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:28.065209+00:00
-- url     : https://prove2.me/theorems/d3251d6c-0c3c-4bd8-a4f0-b0e047103bc8
-- title:
--   Algorithm 1 is well defined: a greedy scenario always exists
-- statement:
--   Let $\mathcal A$ be an online fractional covering algorithm for $M\in\mathbb R^{m\times n}$ and cost $d$. Let $w_{\ell i}$ be weights and $\hat S_1,\dots,\hat S_L\subseteq[m]$ blocks, and set
--   $$\mathcal U_\ell=\Big\{\mathbb 1(b):\ b\subseteq\hat S_\ell,\ \sum_{i\in b}w_{\ell i}\le1\Big\}.$$
--   Then Algorithm 1 has a run. That is, there are a bijection $\sigma$ of $[L]$ (the order in which the blocks are chosen) and sets $a_1,\dots,a_L$ with $a_\ell\in\mathcal U_{\sigma(\ell)}$ such that, at every step $\ell$, the pair $(\sigma(\ell),a_\ell)$ maximizes the online augmenting cost
--   $$\mathcal A(b\mid a_1,\dots,a_{\ell-1})=\mathcal A(a_1,\dots,a_{\ell-1},b)-\mathcal A(a_1,\dots,a_{\ell-1})$$
--   over all blocks $s$ not chosen at an earlier step and all $b\in\mathcal U_s$.
--
--   This guarantees that the greedy scenario on which the construction of Section 4.2 rests always exists.
--
--   **Formalization Note** The run is the predicate `IsGreedyRun alg w Shat σ a` of definition `BudgetedAffine_Disjoint_Construction`; ties in the arg max are arbitrary.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Sec. 4.2, Algorithm 1, p. 17

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- Algorithm 1 is well defined: for every online covering algorithm, weights `w` and blocks
`Ŝ_ℓ`, there is a run `(σ, a)` of Algorithm 1 (at each step an unused block and an admissible
`b ∈ 𝒰_s` maximizing the online augmenting cost). -/
theorem greedy_run_exists {m n L : ℕ} {M : Matrix (Fin m) (Fin n) ℝ} {d : Fin n → ℝ} {ρ : ℝ}
    (alg : OnlineCover M d ρ) (w : Fin L → Fin m → ℝ) (Shat : Fin L → Finset (Fin m)) :
    ∃ (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m)), IsGreedyRun alg w Shat σ a := by sorry

end BudgetedAffine.Disjoint
