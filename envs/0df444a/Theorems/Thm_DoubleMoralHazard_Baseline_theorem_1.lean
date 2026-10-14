-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_theorem_1
-- name    : DoubleMoralHazard.Baseline.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:19.095385+00:00
-- url     : https://prove2.me/theorems/baf064c5-2985-473b-ad8e-f3371d6ed0b0
-- title:
--   Theorem 1, p. 21 — γ¹(w¹), γ²(w²), γ³(w³) is optimal in Γ^IC according as c ≤ µpRᵘ, µpRᵘ < c < µRᵘ, c ≥ µRᵘ
-- statement:
--   Consider the baseline model with parameters satisfying the standing condition (2.5). For $i=1,2,3$ let $F_i$ be the solution of the scenario's value-function equation with $F_i(0)=0$ (Lemma 4: (2.9), the corrected (2.11), (2.13)), and let
--   $$w^i=\arg\max_{w\ge0}F_i(w)\qquad(2.14)$$
--   be its maximizer. Then the optimal contract in the space $\Gamma^{IC}$ of incentive compatible contracts is
--
--   1. $\gamma^1(w^1)$ of Definition 1 if $c\le\mu pR^u$,
--   2. $\gamma^2(w^2)$ of Definition 2 if $\mu pR^u<c<\mu R^u$,
--   3. $\gamma^3(w^3)$ of Definition 3 if $c\ge\mu R^u$,
--
--   in the sense that $\gamma^i(w^i)\in\Gamma^{IC}$ and
--   $$U(\gamma,\bar\nu,N^u)\ \le\ U(\gamma^i(w^i),\bar\nu,N^u)\qquad\text{for every }\gamma\in\Gamma^{IC}.$$
--
--   The theorem identifies the optimal way to motivate an agent who can both shirk and divert unobservable revenue: a probationary period in which promised utility drifts down and jumps up at rewarded arrivals, termination when it reaches zero, and tenure with payments once it reaches the threshold $\bar w^i$; which arrivals are rewarded, and by how much, depends on which incentive constraint binds.
--
--   **Formalization Note** The statement quantifies over every solution $F$ of the scenario's equation and every maximizer $w^i\ge0$ of $F$ on $[0,\infty)$. This is faithful because Lemma 4 gives existence and uniqueness of the solution on $[0,\infty)$, and the paper notes the maximizer is unique; the maximizer lies in $[0,\bar w^i]$ because $F$ decreases with slope $-1$ beyond $\bar w^i$. Both halves of optimality are asserted: membership of $\gamma^i(w^i)$ in $\Gamma^{IC}$ and the comparison with every $\gamma\in\Gamma^{IC}$. $\Gamma^{IC}$ quantifies (IC) over every measurable effort-and-reporting strategy and excludes contracts with infinite expected payments. Scenario 2 uses the corrected (2.11).
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 21, Theorem 1, with (2.14), p. 20, and (2.15), p. 21

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts
import Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts

namespace DoubleMoralHazard.Baseline

/-- Theorem 1, p. 21: the optimal contract in `Γ^IC` is `γ¹(w¹)` if `c ≤ µ p Rᵘ`, `γ²(w²)` if
`µ p Rᵘ < c < µ Rᵘ` and `γ³(w³)` if `c ≥ µ Rᵘ`, where `wⁱ = argmax_{w ≥ 0} Fᵢ(w)` (2.14) and `Fᵢ`
solves the scenario's value-function equation (Lemma 4). "Optimal" means: the contract lies in
`Γ^IC` and no contract in `Γ^IC` gives the principal a larger utility `U(·, ν̄, Nᵘ)`. -/
theorem theorem_1 (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F →
      ∀ w1 : ℝ, 0 ≤ w1 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w1) →
        gamma1 P w1 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma1 P w1)) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ∀ w2 : ℝ, 0 ≤ w2 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w2) →
        gamma2 P w2 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma2 P w2)) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F →
      ∀ w3 : ℝ, 0 ≤ w3 → (∀ w : ℝ, 0 ≤ w → F w ≤ F w3) →
        gamma3 P w3 ∈ GammaIC P ∧ ∀ γ ∈ GammaIC P, U P γ ≤ U P (gamma3 P w3)) := by sorry

end DoubleMoralHazard.Baseline
