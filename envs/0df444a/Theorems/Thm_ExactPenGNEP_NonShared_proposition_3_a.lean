-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_proposition_3_a
-- name    : ExactPenGNEP.NonShared.proposition_3_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:41.457754+00:00
-- url     : https://prove2.me/theorems/0768c10e-639e-4047-aac9-0ebfe3bec41e
-- title:
--   Proposition 3 (a), p. 8 — a penalized equilibrium solves the GNEP iff it lies in graph(X)
-- statement:
--   Consider the GNEP $(C, X; \theta)$ with private sets $C^\nu$, coupled constraint sets $X^\nu(x^{-\nu})$ and costs $\theta_\nu$. Suppose that $C = \prod_\nu C^\nu$ and the graph of the constraint multifunction $X$, $\{x \mid x^\nu \in X^\nu(x^{-\nu}) \ \forall \nu\}$, are closed. For each player $\nu$ let $r_\nu$ be a function of the profile such that, for every $x^{-\nu} \in C^{-\nu}$, $r_\nu(\cdot, x^{-\nu})$ is a $C^\nu$-residual function of $X^\nu(x^{-\nu})$: it is nonnegative, and for $x^\nu \in C^\nu$ it vanishes exactly when $x^\nu \in X^\nu(x^{-\nu})$.
--
--   Let $\rho > 0$ and let $x^*$ be an equilibrium of the penalized NEP $(C; \theta + \rho r_X)$, in which player $\nu$ minimizes $\theta_\nu(x^\nu, x^{*,-\nu}) + \rho\, r_\nu(x^\nu, x^{*,-\nu})$ over $x^\nu \in C^\nu$. Then
--
--   $$x^* \text{ is an equilibrium of the GNEP } (C, X; \theta) \iff x^{*,\nu} \in X^\nu(x^{*,-\nu}) \text{ for all } \nu \in [N].$$
--
--   This is the reduction behind every exact penalization result of the paper: once a penalized equilibrium is shown to be feasible for the coupled constraints, it is an equilibrium of the original game.
--
--   **Formalization Note** $X^\nu(x^{-\nu})$ is a family `X ν x`; the hypothesis that `X ν x` does not change when player $\nu$'s own block of $x$ changes expresses that $X^\nu$ depends on $x^{-\nu}$ only, which is the meaning of the notation. "The graph of $X$" is the set of profiles with $x^\nu \in X^\nu(x^{-\nu})$ for all $\nu$, as the proposition itself explains it. "For all $x^{-\nu} \in C^{-\nu}$" is "for all profiles whose rival blocks lie in their $C^{\nu'}$". The paper omits the proof.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, p. 8, Proposition 3 (a)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem proposition_3_a {N : ℕ} {n : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (X : ∀ ν, Profile n → Set (Strat n ν)) (θ r : Fin N → Profile n → ℝ) (ρ : ℝ) (x : Profile n)
    (hX : ∀ ν (z : Profile n) (y : Strat n ν), X ν (Function.update z ν y) = X ν z)
    (hC : IsClosed (Set.univ.pi C)) (hgraph : IsClosed {z : Profile n | inGraph X z})
    (hr : ∀ ν (z : Profile n), (∀ ν' ≠ ν, z ν' ∈ C ν') →
      IsResidual (fun y => r ν (Function.update z ν y)) (X ν z) (C ν))
    (hρ : 0 < ρ) (hx : IsNashEq C (fun ν y => θ ν y + ρ * r ν y) x) :
    IsGNE C X θ x ↔ inGraph X x := by sorry

end ExactPenGNEP.NonShared
