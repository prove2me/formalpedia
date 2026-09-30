-- Prove2me | Theorems.Thm_BorkarMeynODE_Bounded_psiHat_interp_error_bound
-- name    : BorkarMeynODE.Bounded.psiHat_interp_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:49:08.796292+00:00
-- url     : https://prove2.me/theorems/a4b3a76f-2bdf-4974-ad2f-87ec71bf8d69
-- title:
--   Lemma 4.8 — $\sup_{t\ge0}\mathsf E\|\hat\psi(t)-\psi(t)\|^2 \le C_3\bar\alpha$
-- statement:
--   Assume (A1) for $h$ and $h_\infty$, and let $C_0$ be the constant of (A2). Then there is $\alpha^* > 0$ such that for every block length $T > 0$ and every initial point $x_0 \in \mathbb{R}^d$ there is a constant $C_3 < \infty$ with the following property. Whenever the stepsizes satisfy (BS) with bounds $\underline\alpha < \bar\alpha \le \alpha^*$, $X$ follows the recursion (1.1) with noise $M$ satisfying (A2) with constant $C_0$ and $X(0) = x_0$, and $\hat\psi$ is, on every block $[T(j), T(j+1))$, the solution of (1.2) $\dot x = h(x)$ started from $\psi(T(j))$,
--
--   $$\sup_{t \ge 0} \mathsf E\big[\|\hat\psi(t) - \psi(t)\|^2\big] \le C_3\, \bar\alpha.$$
--
--   Here $\psi$ is the piecewise linear interpolation of the iterates on the ODE time grid $t(n) = \sum_{i<n} a(i)$. The constant $C_3$ may depend on $T$ and $x_0$ but not on the stepsizes. The lemma quantifies how closely the iterates track the ODE (1.2) over blocks of length about $T$ when the stepsize does not vanish; it is the key estimate in the proof of Theorem 2.3.
--
--   **Formalization Note** The paper's $\alpha^*$ is that of Theorem 2.1(ii); here it is existentially quantified in the statement itself. Expectations and the supremum are computed in $[0,\infty]$. The first block, where the error scales with $\|x_0\|^2$, is included in the supremum, which is why $C_3$ may depend on $x_0$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 465, Lemma 4.8

import Mathlib
import Definitions.Def_BorkarMeynODE_Bounded_ODEStability
import Definitions.Def_BorkarMeynODE_Bounded_SAModel
import Definitions.Def_BorkarMeynODE_Bounded_TimeGrid

namespace BorkarMeynODE.Bounded

open MeasureTheory Filter Topology

/-- Lemma 4.8 (Borkar–Meyn 2000, p. 465). Under (A1), (A2) and (BS) there is `α* > 0` such that
for every block length `T > 0` and every deterministic initial condition `x₀` there is a
constant `C₃ < ∞` with `sup_{t ≥ 0} E‖ψ̂(t) − ψ(t)‖² ≤ C₃ ᾱ` whenever `ᾱ ≤ α*`.
Here `ψ` is the interpolated path of the iterates and `ψ̂` is, on each block `[T(j), T(j+1))`,
the solution of (1.2) started from `ψ(T(j))`. `C₃` may depend on `T` and `x₀`, never on the
stepsizes. -/
theorem psiHat_interp_error_bound {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) (C₀ : ℝ) :
    ∃ αstar : ℝ, 0 < αstar ∧
      ∀ T : ℝ, 0 < T → ∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ C₃ : ℝ,
      ∀ (αlo αhi : ℝ) (a : ℕ → ℝ), BoundedStepsize αlo αhi a → αhi ≤ αstar →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n)),
        (∀ n, StronglyMeasurable (M n)) → IsSARecursion h a X M →
        AssumptionA2 P X M hX C₀ → (∀ ω, X 0 ω = x₀) →
        ∀ ψh : Ω → ℝ → EuclideanSpace ℝ (Fin d),
          (∀ ω : Ω, IsPsiHat h a T (interpPath a X ω) (ψh ω)) →
        ⨆ t ∈ Set.Ici (0 : ℝ), ∫⁻ ω, ‖ψh ω t - interpPath a X ω t‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal (C₃ * αhi) := by sorry

end BorkarMeynODE.Bounded
