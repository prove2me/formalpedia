-- Prove2me | Theorems.Thm_BanditCovariates_SE_bound_2_2
-- name    : BanditCovariates.SE.bound_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:05.31083+00:00
-- url     : https://prove2.me/theorems/a1d37e4b-4b5b-4b5c-95f1-378f0eb158cf
-- title:
--   Equation (2.2), p. 7 — bound on the elimination round
-- statement:
--   For a gap $0<\Delta\le1$, $\gamma\ge1$, and integer $T\ge1$, let $\tau$ be the first positive integer round at which $(3/2)\gamma U(\tau,T)\le\Delta$. Then
--
--   $$\tau\le\frac{19\gamma^2}{\Delta^2}\overline{\log}\!\left(\frac{T\Delta^2}{18\gamma^2}\right).$$
--
--   This deterministic estimate limits how long a suboptimal arm can remain active on the good event.
--
--   **Formalization Note** The paper defines $\tau$ as the ceiling of the positive real solution of the corresponding equality. The least-integer formulation gives that ceiling. The upper bound $\Delta\le1$ follows from rewards in $[0,1]$.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 7, (2.2) and its preceding definition of τ_i

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

namespace BanditCovariates.SE

/-- Equation (2.2), p. 7: the deterministic stopping-round upper bound. -/
theorem bound_2_2 (T : ℕ) (hT : 1 ≤ T) (γ Δ : ℝ)
    (hγ : 1 ≤ γ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    (stoppingRound T γ Δ : ℝ) ≤
      (19 * γ ^ 2 / Δ ^ 2) * logbar ((T : ℝ) * Δ ^ 2 / (18 * γ ^ 2)) := by sorry

end BanditCovariates.SE
