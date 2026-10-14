-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_eq_5_1
-- name    : FactorRMDP.ValueIter.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:42.062257+00:00
-- url     : https://prove2.me/theorems/1592e04d-0101-4cd2-a383-4c703f28ab90
-- title:
--   (5.1) — the value of an optimal robust pair is the fixed point of F
-- statement:
--   Consider a robust MDP whose factor matrix uncertainty set is r-rectangular and a discount factor $\lambda\in(0,1)$. There is a solution $(\pi^*,W^*)$ of the robust MDP problem, with $\pi^*$ deterministic, whose value function $v^* = v^{\pi^*,W^*}$ satisfies the fixed-point equality
--
--   $$v^*_s = \max_{a\in\mathbb A}\Big\{ r_{sa} + \lambda\sum_{i=1}^r u^i_{sa}\min_{w_i\in\mathcal W^i} w_i^\top v^*\Big\}, \qquad s\in\mathbb S,$$
--
--   that is, $v^* = F(v^*)$.
--
--   This is the robust optimality equation: it identifies the robust optimal value with the fixed point that Algorithm VI-PI computes.
--
--   **Formalization Note** The paper derives (5.1) for the pair $(\pi^*,W^*)$ of Theorem 4.2. Since (4.6) only holds for a suitably chosen solution (see Theorem 4.2), the statement is in the same existence form. $F$ is in its deterministic form (maximum over actions), which the paper states is equivalent to (5.1).
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), proof of Theorem 5.1, p. 10, (5.1)

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Equation (5.1), proof of Theorem 5.1 (Goyal and Grand-Clément, arXiv:1811.00215v8, p. 10). If
the uncertainty set is r-rectangular, there is a solution `(π*, W*)` of the robust MDP problem with
`π*` deterministic whose value function `v* = v^{π*,W*}` is a fixed point of `F`:
`v*_s = max_{a ∈ 𝔸} { r_sa + λ ∑ᵢ u^i_sa min_{wᵢ ∈ 𝒲ⁱ} wᵢᵀ v* }` for all `s`. Existence form, as in
the corrected Theorem 4.2 from which the paper derives it. -/
theorem eq_5_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    ∃ (πs : S → A → ℝ) (Ws : Fin r → S → ℝ), IsDeterministic πs ∧
      M.IsRobustSolution lam πs Ws ∧ M.F lam (M.value lam πs Ws) = M.value lam πs Ws := by sorry

end FactorRMDP.ValueIter
