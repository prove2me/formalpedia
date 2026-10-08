-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_theorem_3
-- name    : AdaptiveEM.Finite.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:43.768275+00:00
-- url     : https://prove2.me/theorems/770a370b-8ba1-4929-8dee-c9aab24f4752
-- title:
--   Theorem 3 (Strong convergence order), p. 531 — E[sup_{0≤t≤T} ‖X̂_t − X_t‖^p] ≤ C_{p,T} δ^{p/2}
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$. Let $f:\mathbb R^m\to\mathbb R^m$ and $g:\mathbb R^m\to\mathbb R^{m\times d}$ satisfy Assumption 4, let $x_0\in\mathbb R^m$ and $T>0$, and let $X$ be a solution on $[0,T]$ of
--   $$dX_t=f(X_t)\,dt+g(X_t)\,dW_t,\qquad X_0=x_0 .$$
--   Let $h$ satisfy Assumption 2 and let the timestep functions $h^\delta$, $0<\delta\le1$, satisfy Assumption 3, each $h^\delta$ measurable. Write $\widehat X$ for the continuous interpolant of the adaptive scheme (5) run with $h^\delta$ from $x_0$. Then for every $p>0$ there is a constant $C_{p,T}$ such that for all $\delta\in(0,1]$
--   $$\mathbb E\Big[\sup_{0\le t\le T}\|\widehat X_t-X_t\|^p\Big]\le C_{p,T}\,\delta^{p/2}.$$
--
--   The adaptive explicit scheme therefore converges strongly with order $\tfrac12$ in $\delta$, the order of the uniform-step Euler–Maruyama method under global Lipschitz conditions, for drifts that are only one-sided Lipschitz with polynomial growth.
--
--   **Formalization Note** The constant is chosen before $\delta$, as a rate requires. $X$ is any process satisfying the published solution relation; existence and uniqueness are not part of the claim. Assumption 1 is not a hypothesis: Assumption 4 implies it (p. 531). Measurability of each $h^\delta$ is an added regularity hypothesis (Assumption 3 states only (11)); continuity of $h^\delta$ is not assumed. The expectation is a $[0,\infty]$-valued integral.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 531, Theorem 3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), Theorem 3 (strong convergence order), p. 531: under Assumption 4, with
`h^δ` satisfying Assumption 3 for an `h` satisfying Assumption 2, for every `p > 0` there is a
constant `C_{p,T}` (independent of `δ`) such that for all `δ ∈ (0, 1]`
`E[sup_{0≤t≤T} ‖X̂_t - X_t‖^p] ≤ C_{p,T} δ^{p/2}`, where `X̂` is the continuous interpolant of
the adaptive scheme run with `h^δ` and `X` is any solution of the SDE on `[0, T]`. -/
theorem theorem_3 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α γ μ q : ℝ) (hA4 : Assumption4 f g α γ μ q)
    (h : SDEState m → ℝ) (α' β' : ℝ) (hA2 : Assumption2 f h α' β')
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T)
    (hδ : ℝ → SDEState m → ℝ) (hA3 : Assumption3 (T : ℝ) h hδ)
    (hδ_meas : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Measurable (hδ δ))
    (X : ℝ≥0 → Ω → SDEState m)
    (hX : SabanisEuler.Shared.IsSolution P ℱ W T (fun _ => x0) (fun z => f z.2)
      (fun z => g z.2) X) :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖Xhat f g (hδ δ) x0 W t ω - X t ω‖ₑ) ^ p ∂P
        ≤ ENNReal.ofReal (C * δ ^ (p / 2)) := by sorry

end AdaptiveEM.Finite
