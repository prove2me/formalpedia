-- Prove2me | Theorems.Thm_EthierKurtz_sde_stability_in_probability
-- name    : EthierKurtz.sde_stability_in_probability
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:08:56.324047+00:00
-- url     : https://prove2.me/theorems/b8e73878-9ab8-49f7-b02c-b8c62ab27bcb
-- title:
--   Stability in probability of a locally Lipschitz SDE solution against Itô processes with nearby coefficients
-- statement:
--   Let $X$ solve $dX=\sigma_0(X)\,dW+b_0(X)\,dt$, $X_0=x_0$, with $\sigma_0,b_0$ continuous, $L$-Lipschitz and bounded by $S$ on $\bar B_{R+3}$. For every $t\ge 0$ and $\varepsilon,\eta>0$ there is $\delta>0$ such that for every continuous adapted Itô process $Y=x_0+\int H^Y dW+\int b^Y du$ with $|H^Y|,|b^Y|\le S$,
--
--   $$\mathbb E\int_0^t \mathbf 1_{|Y_u|\le R+3}\big(|b_0(Y_u)-b^Y_u|^2+|\sigma_0(Y_u)-H^Y_u|^2\big)\,du\le\delta \;\Longrightarrow\; \mathbb P\Big(\sup_{s\le t}|X_s|\le R,\ |X_t-Y_t|^2>\varepsilon\Big)\le\eta .$$
--
--   (The integrated mismatch is bounded through any continuous nonnegative majorant $e$.)
--
--   Role: the localized stability estimate that turns convergence of approximation coefficients into convergence in probability of the approximations to the SDE solution, before the solution leaves the ball of radius $R$.
-- source:
--   D. J. Higham, X. Mao, A. M. Stuart, Strong convergence of Euler-type methods for nonlinear stochastic differential equations, SIAM J. Numer. Anal. 40 (2002) 1041-1063, https://doi.org/10.1137/S0036142901389530, Theorem 2.2 and its proof (localization at the exit time of the ball of radius R)

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

theorem sde_stability_in_probability {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {R L S : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 3 → ‖y‖ ≤ R + 3 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hS0 : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (t : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Y : ℝ≥0 → Ω → SDEState d) (HY JY : ℝ≥0 → Ω → SDEDiffusion d)
      (bY : ℝ≥0 → Ω → SDEState d) (e : ℝ → Ω → ℝ),
      (∀ s, Measurable (Y s)) → (∀ ω, Continuous fun s => Y s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s)) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s)) →
      (∀ ω, Continuous fun s => HY s ω) →
      (∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s)) →
      (∀ ω, Continuous fun s => bY s ω) →
      (∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j))) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
        ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i) →
      (∀ᵐ ω ∂P, Y 0 ω = x₀) →
      (∀ s ω, ‖HY s ω‖ ≤ S) → (∀ s ω, ‖bY s ω‖ ≤ S) →
      (∀ ω, Continuous fun u => e u ω) → (∀ u ω, 0 ≤ e u ω) →
      (∀ u ω, ‖Y u.toNNReal ω‖ ≤ R + 3 →
        ‖b₀ (Y u.toNNReal ω) - bY u.toNNReal ω‖ ^ 2 +
          ‖σ₀ (Y u.toNNReal ω) - HY u.toNNReal ω‖ ^ 2 ≤ e u ω) →
      Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, e u ω) P →
      ∫ ω, (∫ u in (0 : ℝ)..t.val, e u ω) ∂P ≤ δ →
      P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ‖X t ω - Y t ω‖ ^ 2} ≤ ENNReal.ofReal η := by sorry

end EthierKurtz
