-- Prove2me | Theorems.Thm_CondPortOT_SingDual_proposition_2_5
-- name    : CondPortOT.SingDual.proposition_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:47.083998+00:00
-- url     : https://prove2.me/theorems/9f9cadfc-09dd-4ba3-9f86-727e93e23578
-- title:
--   Proposition 2.5, p. 11 — ρ_min is the value of the knapsack LP (9), and a feasible ℚ ∈ 𝔹_ρ exists iff ρ ≥ ρ_min
-- statement:
--   Let $\gamma\ge0$, $\varepsilon\in[0,1]$, $N\ge1$, and assume Assumption 2.4. With $\kappa_i$ the projection costs of (7):
--
--   1. The value $\rho_{\min}(x_0,\gamma,\varepsilon)$ equals the optimal value of the linear program
--   $$\rho_{\min}(x_0,\gamma,\varepsilon)=\min\Big\{N^{-1}\sum_{i\in[N]}\kappa_i\upsilon_i:\ \upsilon\in[0,1]^N,\ \sum_{i\in[N]}\upsilon_i\ge N\varepsilon\Big\},$$
--   and the minimum is attained.
--   2. For every $\rho\ge0$, there exists $\mathbb Q\in\mathbb B_\rho$ with $\mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon$ if and only if $\rho\ge\rho_{\min}(x_0,\gamma,\varepsilon)$.
--
--   This identifies the threshold radius above which the robust conditional problem is feasible, and computes it as a fractional knapsack problem.
--
--   **Formalization Note** "min" is stated as attainment (`IsLeast`) of the LP value $v$, and $\rho_{\min}$ (a $[0,\infty]$-valued infimum) equals $v$. The equivalence in part 2 is stated for $\rho\ge0$, as the paper's $\rho\in\mathbb R_+$. $\kappa_i$ is the infimum of $\mathbb D_{\mathcal X}(\cdot,\hat x_i)$ over $\mathcal N_\gamma(x_0)$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 11, Proposition 2.5, display (9); proof pp. 34–35

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem proposition_2_5 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 ≤ γ) (hA : Assumption24 DX DY x0 γ xh)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∃ v : ℝ,
        IsLeast {r : ℝ | ∃ υ : Fin N → ℝ, (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧
            (N : ℝ) * ε ≤ ∑ i, υ i ∧ r = (N : ℝ)⁻¹ * ∑ i, CondPortOT.SingUninf.kappa DX x0 γ xh i * υ i} v ∧
          rhoMin DX DY xh yh x0 γ ε = ENNReal.ofReal v) ∧
      ∀ ρ : ℝ, 0 ≤ ρ →
        ((∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 γ)) ↔
          rhoMin DX DY xh yh x0 γ ε ≤ ENNReal.ofReal ρ) := by sorry

end CondPortOT.SingDual
