-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_theorem_6
-- name    : AdaptiveEM.Infinite.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:10.257215+00:00
-- url     : https://prove2.me/theorems/65251988-e1d7-48ae-86fe-269ff50875cd
-- title:
--   Theorem 6 (Strong convergence order in infinite time interval) — $\mathbb E\|\widehat X_t-X_t\|^p\le C_p\delta^{p/2}$ for all $t\ge0$
-- statement:
--   Let $W$ be a $d$-dimensional standard Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$, and consider the SDE
--   $$\mathrm dX_t=f(X_t)\,\mathrm dt+g(X_t)\,\mathrm dW_t,\qquad X_0=x_0\in\mathbb R^m,$$
--   with $X$ a solution on $[0,\infty)$. Assume:
--   1. $f,g$ satisfy Assumption 9: for some $p^*\in(2,\infty)$ and $\lambda,\eta>0$, $\langle x-y,f(x)-f(y)\rangle+\frac{p^*-1}2\|g(x)-g(y)\|^2\le-\lambda\|x-y\|^2$, $\|g(x)-g(y)\|^2\le\eta\|x-y\|^2$, and $\|f(x)-f(y)\|\le(\gamma(\|x\|^q+\|y\|^q)+\mu)\|x-y\|$ with $\gamma,\mu,q>0$;
--   2. $g$ is bounded: $\|g(x)\|^2\le\beta_g$ for all $x$;
--   3. $h$ satisfies Assumption 8 (continuous, $0<h\le h_{\max}$, and $\langle x,f(x)\rangle+\frac12h(x)\|f(x)\|^2\le-\alpha\|x\|^2+\beta$);
--   4. for a fixed $T>0$ and every $\delta\in(0,1]$, the timestep $h^\delta$ is measurable and satisfies $\delta\min(T,h(x))\le h^\delta(x)\le\min(\delta T,h(x))$.
--
--   Let $\widehat X$ denote the continuous interpolant of the adaptive Euler–Maruyama scheme run with timestep $h^\delta$. Then for every $p\in(0,p^*]$ there is a constant $C_p$ such that
--   $$\mathbb E\big[\|\widehat X_t-X_t\|^p\big]\le C_p\,\delta^{p/2}\qquad\text{for all }\delta\in(0,1]\text{ and all }t\ge0.$$
--
--   The adaptive scheme thus converges strongly with order $\tfrac12$ in $\delta$, with an error bound that does not grow with time. This is what makes long-time simulation of contractive ergodic SDEs with non-globally Lipschitz drift reliable, and it is the basis of the paper's multilevel Monte Carlo estimator for invariant measures.
--
--   **Formalization Note** The boundedness of $g$ (item 2) is not in the printed statement of Theorem 6, whose hypothesis is Assumption 9. The proof (§6.4, p. 558) bounds the moments of the numerical solution "due to the stability property in Theorem 5", whose hypothesis Assumption 7 includes $\|g(x)\|^2\le\beta$; Assumption 9 implies the rest of Assumption 7 but not this bound, and the introduction (p. 527) places the infinite-time analysis in the setting of "a bounded and non-degenerate diffusion coefficient $g$". The hypothesis is therefore made explicit. Measurability of $h^\delta$ is assumed because Assumption 3 states no regularity. The constant $C_p$ is chosen before $\delta$ and $t$. Expectations are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 534, Theorem 6 (bounded g: p. 527 and the use of Theorem 5 on p. 558)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 534, Theorem 6 (strong convergence order in infinite time
interval): if `f, g` satisfy Assumption 9, `g` is bounded (`‖g(x)‖² ≤ β_g`, (18), the standing
bounded-diffusion assumption of the ergodic setting, p. 527), `h` satisfies Assumption 8 and
the family `h^δ`, `δ ∈ (0, 1]`, satisfies Assumption 3 for a fixed `T > 0` with each `h^δ`
measurable, and `X` solves the SDE from `x0` on `[0, ∞)`, then for every `p ∈ (0, p*]` there is
`C_p` with `E‖X̂_t − X_t‖^p ≤ C_p δ^{p/2}` for all `δ ∈ (0, 1]` and all `t ≥ 0`, where `X̂` is
the continuous interpolant of the scheme run with timestep `h^δ`. -/
theorem theorem_6 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (x0 : SDEState m)
    (pstar lam η γ μ q : ℝ) (hA9 : Assumption9 f g pstar lam η γ μ q)
    (βg : ℝ) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ βg)
    (h : SDEState m → ℝ) (hmax α β : ℝ) (hA8 : Assumption8 f h hmax α β)
    (T : ℝ) (hT : 0 < T) (hδ : ℝ → SDEState m → ℝ)
    (hA3 : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Assumption3 h T δ (hδ δ) ∧ Measurable (hδ δ))
    (X : ℝ≥0 → Ω → SDEState m)
    (hX : ∀ T' : ℝ≥0, IsSolution P ℱ W T' (fun _ => x0) (fun z => f z.2) (fun z => g z.2) X) :
    ∀ p : ℝ, 0 < p → p ≤ pstar → ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ t : ℝ≥0,
      ∫⁻ ω, ‖AdaptiveEM.Finite.Xhat f g (hδ δ) x0 W t ω - X t ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal (C * δ ^ (p / 2)) := by sorry

end AdaptiveEM.Infinite
