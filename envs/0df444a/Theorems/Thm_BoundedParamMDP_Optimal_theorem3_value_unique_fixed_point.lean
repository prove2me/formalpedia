-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_theorem3_value_unique_fixed_point
-- name    : BoundedParamMDP.Optimal.theorem3_value_unique_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:27.337865+00:00
-- url     : https://prove2.me/theorems/57df887e-66d9-49cb-8e08-82459cd48559
-- title:
--   Theorem 3 (second sentence) — $V_{M,\pi}$ is the unique fixed point of $VI_{M,\pi}$
-- statement:
--   Let $M$ be an exact MDP with finite state set $Q$, discount rate $0\le\gamma<1$, and let $\pi:Q\to A$ be a policy. The value function $V_{M,\pi}$ (the expected discounted cumulative reward of $\pi$) is a fixed point of the value-iteration operator $VI_{M,\pi}$, and it is the only one:
--   $$
--   VI_{M,\pi}(V_{M,\pi})=V_{M,\pi},\qquad\text{and}\qquad VI_{M,\pi}(v)=v\ \Longrightarrow\ v=V_{M,\pi}\quad\text{for every }v:Q\to\mathbb R.
--   $$
--   Equivalently, $V_{M,\pi}$ is the unique solution of the Bellman equation (2), $V_{M,\pi}(p)=R(p)+\gamma\sum_{q}F_{pq}(\pi(p))V_{M,\pi}(q)$.
--
--   This is the fact from the theory of exact MDPs that the proofs of the paper's interval results use whenever they pass between a value function and the operator $VI_{M,\pi}$.
--
--   **Formalization Note** Only the second sentence of Theorem 3 is formalized; its first sentence concerns the optimal value function $V^*$ of an exact MDP, which this mission does not use.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 7, Theorem 3 (second sentence)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP

namespace BoundedParamMDP.Optimal

/-- Theorem 3, second sentence (Givan–Leach–Dean 2000, p. 7): `V_{M,π}` is the unique fixed
point of `VI_{M,π}`. -/
theorem theorem3_value_unique_fixed_point {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] (M : MDP Q A) (π : Policy Q A) :
    VIpol M π (value M π) = value M π ∧
      ∀ v : Q → ℝ, VIpol M π v = v → v = value M π := by sorry

end BoundedParamMDP.Optimal
