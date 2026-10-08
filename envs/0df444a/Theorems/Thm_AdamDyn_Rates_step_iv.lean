-- Prove2me | Theorems.Thm_AdamDyn_Rates_step_iv
-- name    : AdamDyn.Rates.step_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:09.494422+00:00
-- url     : https://prove2.me/theorems/f16dc3aa-29da-414a-a06c-9b89fa10797b
-- title:
--   §7.4 iv) — after normalising $\ell=0$, $\dot w_\delta\le -c_4\,w_\delta^{2(1-\theta)}$ eventually
-- statement:
--   Assume the hypotheses of Theorem 3.4: $F$ is $C^1$ with locally Lipschitz gradient, coercive, and has the Łojasiewicz property (Assumption 3.3); $S$ is locally Lipschitz and coordinatewise positive; $a,b>0$, $b\le4a$, $\varepsilon>0$; $F(\mathcal S)$ has empty interior. Let $z(t)=(x(t),m(t),v(t))$ be a global solution of the Adam ODE with initial condition $(x_0,0,0)$.
--
--   Let $\ell:=\lim_{t\to\infty}F(x(t))$ and replace $F$ by $F-\ell$, so that $\ell=0$ (step iii) of the proof). Write $w_\delta(t)=\tilde W_\delta(t,z(t))$ for the function (7.11) built from $F-\ell$. Then there exist $\delta>0$, an exponent $\theta\in(0,\tfrac12]$, a constant $c_4>0$ and a time $T'\ge1$ such that for almost every $t\ge T'$, $w_\delta$ is differentiable at $t$ and
--
--   $$\frac{d}{dt}w_\delta(t)\ \le\ -c_4\,w_\delta(t)^{2(1-\theta)} .$$
--
--   Integrating this differential inequality gives the decay of $w_\delta$ (polynomial for $\theta<\tfrac12$, exponential for $\theta=\tfrac12$) that the final step converts into the convergence rate of $x(t)$.
--
--   **Formalization Note** $\ell$ is Mathlib's `limUnder atTop (fun t => F (x t))`; the limit exists under these hypotheses, so this is the paper's $\ell$. The replacement of $F$ by $F-\ell$ changes neither $\nabla F$ nor the ODE; it shifts $w_\delta$ by $-\ell$. The paper derives the display assuming $w_\delta>0$ on $[1,\infty)$ (the other case ends the proof); the statement here carries no positivity assumption: $w_\delta$ (built from $F-\ell$) is nonnegative on $[1,\infty)$ for the $\delta$ of (7.13), and if it vanishes at some time it stays $0$ afterwards, where the inequality reads $0\le0$. The power is the real power of a nonnegative number.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 20–21, §7.4 steps iii)–iv), final display of step iv)

import Mathlib
import Definitions.Def_AdamDyn_Rates_Lojasiewicz
import Definitions.Def_AdamDyn_Rates_AdamField
import Definitions.Def_AdamDyn_Rates_Lyapunov

open Filter Topology MeasureTheory

namespace AdamDyn.Rates

/-- §7.4 step iv), final display (Barakat–Bianchi, p. 21). Let `ℓ := lim_{t→∞} F(x(t))` and
replace `F` by `F − ℓ` (the normalisation of step iii)); write `w_δ` for the function (7.11)
built from `F − ℓ` along the global solution `z` from `(x0, 0, 0)`. Under the hypotheses of
Theorem 3.4 there exist `δ > 0`, a Łojasiewicz exponent `θ ∈ (0, 1/2]`, `c4 > 0` and `T' ≥ 1`
such that for almost every `t ≥ T'`, `w_δ` is differentiable at `t` and
`(d/dt) w_δ(t) ≤ −c4 w_δ(t)^{2(1−θ)}`. -/
theorem step_iv {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hLoj : LojasiewiczProperty F)
    (hint : interior (F '' critSet F) = ∅)
    (hz : IsGlobalSolution F S a b ε x0 z) :
    let Fℓ : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun x => F x - limUnder atTop (fun t => F (z t).1)
    ∃ δ > 0, ∃ θ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ c4 > 0, ∃ T' ≥ (1 : ℝ),
      ∀ᵐ t ∂(volume : Measure ℝ), T' ≤ t →
        DifferentiableAt ℝ (wδ Fℓ S a b ε δ z) t ∧
          deriv (wδ Fℓ S a b ε δ z) t ≤ -c4 * (wδ Fℓ S a b ε δ z t) ^ (2 * (1 - θ)) := by sorry

end AdamDyn.Rates
