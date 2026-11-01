-- Prove2me | Theorems.Thm_EthierKurtz_sde_stability_initial_condition
-- name    : EthierKurtz.sde_stability_initial_condition
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T06:24:13.605134+00:00
-- url     : https://prove2.me/theorems/262c6ecb-47c6-4037-ae43-606fb4c0c7e8
-- title:
--   Stability in probability of a locally Lipschitz SDE solution with respect to the initial point
-- statement:
--   Let $X$ solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=x_0$, with $\sigma_0,b_0$ continuous, $L$-Lipschitz and bounded by $S$ on $\bar B_{R+4}$. For every $t\ge0$ and $\varepsilon,\eta>0$ there is $\delta>0$ such that every solution $Y$ of the same equation, driven by the same Brownian motion, with $Y_0=y$ and $|y-x_0|<\delta$ satisfies
--   $$\mathbb P\Big(\sup_{s\le t}|X_s|\le R,\ |X_t-Y_t|^2>\varepsilon\Big)\le\eta .$$
--
--   Role: continuous dependence on the initial point in probability (localized at the ball of radius $R$), from which the Feller property of the stochastic Kolmogorov system follows.
-- source:
--   D. J. Higham, X. Mao, A. M. Stuart, Strong convergence of Euler-type methods for nonlinear stochastic differential equations, SIAM J. Numer. Anal. 40 (2002) 1041-1063, https://doi.org/10.1137/S0036142901389530, Theorem 2.2 and its proof (localization at the exit time of a ball), applied to two solutions with different initial points; cf. X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood 2007, Section 2.3 (continuous dependence on initial values)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem sde_stability_initial_condition {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {R L S : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 4 → ‖y‖ ≤ R + 4 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 4 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (x₀ : SDEState d) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (t : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (y : SDEState d) (Y : ℝ≥0 → Ω → SDEState d), ‖y - x₀‖ < δ →
      SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Y →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η := by sorry

end EthierKurtz
