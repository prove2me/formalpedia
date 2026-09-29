-- Prove2me | Theorems.Thm_ClayNavierStokes_clay_millennium_prize
-- name    : ClayNavierStokes.clay_millennium_prize
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:35:24.514262+00:00
-- url     : https://prove2.me/theorems/63d3ea4c-fbe8-44b9-8506-f61a71267cc6
-- title:
--   Clay Millennium Problem: one of (A), (B), (C), (D) holds
-- statement:
--   The Clay Millennium Prize problem on the Navier–Stokes equations asks for a proof of **one** of four statements. Write $(A)$–$(D)$ for the four propositions (stated in full in the milestones of this mission):
--
--   1. $(A)$: for all $\nu>0$ and every smooth, divergence-free $u_0$ on $\mathbb R^3$ satisfying the decay condition (4), the unforced equations (1)–(3) have a smooth solution on $\mathbb R^3\times[0,\infty)$ with bounded energy (6), (7).
--   2. $(B)$: the same on the torus $\mathbb R^3/\mathbb Z^3$ with conditions (8), (10), (11).
--   3. $(C)$: for all $\nu>0$ there are smooth decaying data $u_0$, $f$ satisfying (4), (5) for which no solution of (1), (2), (3), (6), (7) exists.
--   4. $(D)$: the same on the torus with data satisfying (8), (9) and no solution of (1), (2), (3), (10), (11).
--
--   $$ (A)\ \lor\ (B)\ \lor\ (C)\ \lor\ (D). $$
--
--   This is the formal target of the prize as stated by Fefferman.
--
--   **Formalization Note** Time derivatives are one-sided at $t=0$ (taken within $[0,\infty)$, resp. $[0,T)$); solutions are functions on $\mathbb R^n\times\mathbb R$ constrained only for $t\ge0$; the torus is encoded by $1$-periodicity on $\mathbb R^3$. Definitions come from `Definitions.Def_ClayNavierStokes_defs`.
-- source:
--   C. L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation, Clay Mathematics Institute Millennium Prize Problem description, https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf, p. 2, the four statements (A)–(D) ('we ask for a proof of one of the following four statements'), with equations (1)–(11) on pp. 1–2 and the errata (periodic pressure).

import Definitions.Def_ClayNavierStokes_defs
import Mathlib

namespace ClayNavierStokes

theorem clay_millennium_prize :
    (∀ nu : ℝ, 0 < nu →
      ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), InitialVelocityConditionDecay u₀ →
        ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ 0 v p) ∨
    (∀ nu : ℝ, 0 < nu →
      ∀ u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), InitialVelocityConditionPeriodic u₀ →
        ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ 0 v p) ∨
    (∀ nu : ℝ, 0 < nu →
      ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
        InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
        ¬ ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) ∨
    (∀ nu : ℝ, 0 < nu →
      ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
        InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
        ¬ ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by sorry

end ClayNavierStokes
