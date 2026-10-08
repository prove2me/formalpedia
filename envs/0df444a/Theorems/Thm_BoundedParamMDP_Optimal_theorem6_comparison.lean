-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_theorem6_comparison
-- name    : BoundedParamMDP.Optimal.theorem6_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:30.30383+00:00
-- url     : https://prove2.me/theorems/1f33e3e8-b720-4b53-8153-b284c725c490
-- title:
--   Theorem 6 — $u\le_{\mathrm{dom}}VI_{M,\pi}(u)$ implies $u\le_{\mathrm{dom}}V_{M,\pi}$, and likewise for $\ge$, $<$, $>$
-- statement:
--   Let $M$ be an exact MDP with finite state set $Q$ and discount rate $0\le\gamma<1$, let $\pi$ be a policy and $u:Q\to\mathbb R$ a value function. Then
--
--   1. if $u\le_{\mathrm{dom}}VI_{M,\pi}(u)$ then $u\le_{\mathrm{dom}}V_{M,\pi}$;
--   2. if $u\ge_{\mathrm{dom}}VI_{M,\pi}(u)$ then $u\ge_{\mathrm{dom}}V_{M,\pi}$;
--   3. if $u<_{\mathrm{dom}}VI_{M,\pi}(u)$ then $u<_{\mathrm{dom}}V_{M,\pi}$;
--   4. if $u>_{\mathrm{dom}}VI_{M,\pi}(u)$ then $u>_{\mathrm{dom}}V_{M,\pi}$.
--
--   Here $\le_{\mathrm{dom}}$ is the statewise order and $V_1<_{\mathrm{dom}}V_2$ means $V_1\le_{\mathrm{dom}}V_2$ with strict inequality at some state.
--
--   This comparison principle is how the paper certifies that one MDP or policy is at least as good as another: it suffices to exhibit a function $u$ improved by one application of $VI_{M,\pi}$.
--
--   **Formalization Note** The theorem is about an arbitrary exact MDP, not only members of a BMDP. $V_1>_{\mathrm{dom}}V_2$ is written `domLT V₂ V₁`.
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 7, Theorem 6

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP

namespace BoundedParamMDP.Optimal

/-- Theorem 6 (p. 7): for an exact MDP `M`, a policy `π` and `u : Q → ℝ`,
`u ≤_dom VI_{M,π}(u)` implies `u ≤_dom V_{M,π}`, `u ≥_dom VI_{M,π}(u)` implies
`u ≥_dom V_{M,π}`, and likewise for the strict orders `<_dom` and `>_dom`. -/
theorem theorem6_comparison {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (M : MDP Q A) (π : Policy Q A) (u : Q → ℝ) :
    (u ≤ VIpol M π u → u ≤ value M π) ∧
    (VIpol M π u ≤ u → value M π ≤ u) ∧
    (domLT u (VIpol M π u) → domLT u (value M π)) ∧
    (domLT (VIpol M π u) u → domLT (value M π) u) := by sorry

end BoundedParamMDP.Optimal
