-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_theorem_4_2
-- name    : DynReinsDiv.Barriers.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:22.213246+00:00
-- url     : https://prove2.me/theorems/23bd441e-43fb-4760-a56e-9a4dbfb16cc3
-- title:
--   Theorem 4.2 (without d(∞) and the C^∞ clause) — d(τ) continuous, nondecreasing, d(0+) = 0 < d(τ) ≤ x₂
-- statement:
--   Let $v$ be the solution of the HJB variational inequality of Theorem 3.1 (with $0<\gamma<\mu_1$), written in the variables $(x,\tau)$, $\tau\in(0,T]$ the time to maturity. Let $d(\tau)=\inf\{x\ge0: v_x(x,\tau)=1\}$ be the dividend-payout boundary. Then:
--   1. for every $\tau\in(0,T]$ the set $\{x\ge0: v_x(x,\tau)=1\}$ is nonempty;
--   2. $d$ is continuous and nondecreasing on $(0,T]$;
--   3. $d(\tau)\to0$ as $\tau\to0+$;
--   4. for every $\tau\in(0,T]$,
--   $$0<d(\tau)\le x_2=\sqrt{\frac{1}{\gamma c^3}\,(\mu_1+c\gamma)\,(c\mu_2+\gamma^2)}. \tag{4.3}$$
--
--   The theorem locates the optimal dividend barrier: dividends are paid when the surplus exceeds $d(\tau)$, and the barrier is bounded uniformly in the horizon by an explicit constant.
--
--   **Formalization Note** The paper's statement also has $d(\tau)\le d(\infty)$ and, for bounded claims, $d\in C^\infty(0,T)$; neither is included (the solution lives on a finite horizon, and the smoothness clause is only sketched in the paper). Nonemptiness is part of the conclusion because Lean's infimum of the empty set is $0$. The constant $x_2$ is the closed form printed in (4.3).
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 13, Theorem 4.2, (4.3)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries

namespace DynReinsDiv.Barriers

/-- Theorem 4.2 (arXiv:2008.00391v3, p. 13), without the clauses on `d(∞)` and on `C^∞` regularity
for bounded claims: for the solution `v` of Theorem 3.1 (second argument `τ`), the set
`{x ≥ 0 | v_x(x, τ) = 1}` is nonempty for every `τ ∈ (0, T]`, and the dividend-payout boundary
`d(τ) = inf{x ≥ 0 | v_x(x, τ) = 1}` is continuous and nondecreasing on `(0, T]`, tends to `0` as
`τ → 0+`, and satisfies `0 < d(τ) ≤ x₂ = √((μ₁ + cγ)(cμ₂ + γ²)/(γc³))` (the closed form printed
in (4.3)). -/
theorem theorem_4_2 (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) :
    (∀ τ ∈ Set.Ioc 0 M.T, {x : ℝ | 0 ≤ x ∧ vx x τ = 1}.Nonempty) ∧
    ContinuousOn (dBoundary vx) (Set.Ioc 0 M.T) ∧
    MonotoneOn (dBoundary vx) (Set.Ioc 0 M.T) ∧
    Filter.Tendsto (dBoundary vx) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ τ ∈ Set.Ioc 0 M.T, 0 < dBoundary vx τ ∧
      dBoundary vx τ ≤
        Real.sqrt (1 / (M.γ * M.c ^ 3) * (M.μ₁ + M.c * M.γ) * (M.c * M.μ₂ + M.γ ^ 2))) := by sorry

end DynReinsDiv.Barriers
