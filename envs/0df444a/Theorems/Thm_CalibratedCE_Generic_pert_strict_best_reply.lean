-- Prove2me | Theorems.Thm_CalibratedCE_Generic_pert_strict_best_reply
-- name    : CalibratedCE.Generic.pert_strict_best_reply
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:09:24.47505+00:00
-- url     : https://prove2.me/theorems/6ea6acf3-4f1c-4d5a-979f-968afc0f2532
-- title:
--   Proof of Theorem 2 (p. 48) — the perturbed forecasts $p_i^{x'}$ converge to $p^*$ and have $x'$ as unique best reply
-- statement:
--   Let $p^*\in M_b(x')$, i.e. $p^*$ is a probability vector over $S(2)$ to which $x'$ is a best response of player 1, and let $q$ be a probability vector to which $x'$ is the unique best response: $\sum_y q(y)u_1(x'',y) < \sum_y q(y)u_1(x',y)$ for all $x''\ne x'$. Define
--   $$p_i = \left(1-\tfrac1i\right)p^* + \tfrac1i\,q,\qquad i = 1,2,\dots$$
--   Then for every $i\ge 1$, $p_i$ is a probability vector and $x'$ is its unique best response, and $p_i \to p^*$ as $i\to\infty$.
--
--   In the paper: "Define a sequence $p_i^{x'} = (1 - 1/i)p^* + (1/i)p^{x'}$. Then $p_i^{x'}$ converges to $p^*$ and, for all $i$, $p_i^{x'}$ has $x'$ as its unique best reply." It is what makes the best-reply function well defined when two strategies share the same conditional forecast $p^*$.
--
--   **Formalization Note** The hypothesis $p^*\in M_b(x')$ is implicit on the page ($x'$ is played at the forecast $p^*$ in a CE). The convergence is coordinatewise in $\mathbb{R}^n$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 48, proof of Theorem (Theorem 2)

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

theorem pert_strict_best_reply {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m)
    (pstar q : Fin n → ℝ) (hpstar : pstar ∈ Mb u₁ a) (hq : IsDist q)
    (hqa : ∀ a', a' ≠ a → ∑ b, q b * u₁ a' b < ∑ b, q b * u₁ a b) :
    (∀ i : ℕ, 1 ≤ i → IsDist (pert pstar q i) ∧
        ∀ a', a' ≠ a → ∑ b, pert pstar q i b * u₁ a' b < ∑ b, pert pstar q i b * u₁ a b) ∧
      Tendsto (pert pstar q) atTop (𝓝 pstar) := by sorry

end CalibratedCE.Generic
