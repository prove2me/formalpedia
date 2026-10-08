-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_theorem_1
-- name    : AdaptiveEM.Finite.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:36.651286+00:00
-- url     : https://prove2.me/theorems/124db7c4-d01d-4b63-bf12-b3b7dd546782
-- title:
--   Theorem 1 (Finite time stability), p. 529 — T is a.s. attained and E[sup_{0≤t≤T} ‖X̂_t‖^p] < C_{p,T}, uniformly in h
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$, $(\mathcal F_t)$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$ be given. Let $f,g$ satisfy Assumption 1, fix constants $\alpha,\beta$, an initial value $x_0$ and $T>0$. For every $p>0$ there is a constant $C_{p,T}$ such that, for every timestep function $h$ satisfying Assumption 2 with the constants $\alpha,\beta$, the adaptive scheme (5) satisfies:
--
--   1. $T$ is almost surely attainable: $\mathbb P(\exists N<\infty:\ t_N\ge T)=1$;
--   2. the continuous interpolant has bounded moments:
--   $$\mathbb E\Big[\sup_{0\le t\le T}\|\widehat X_t\|^p\Big]<C_{p,T} .$$
--
--   The theorem shows that the adaptive explicit scheme neither stalls before $T$ nor blows up in moments, for drifts of superlinear growth for which the uniform-step Euler–Maruyama scheme has divergent moments. Because the constant does not depend on $h$, it applies uniformly to every smaller timestep function, which is how Theorem 3 uses it.
--
--   **Formalization Note** The paper says $C_{p,T}$ "depends solely on $p$, $T$ and the constants $\alpha,\beta$ in Assumption 2"; its proof also uses $\|X_0\|$ and the constants of Assumption 1. Here the constant is chosen after $f$, $g$, $x_0$, the constants of Assumption 1 and the probability space, and before $h$: the formal content of the paper's claim is independence of $h$. The expectation is a $[0,\infty]$-valued integral.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 529, Theorem 1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), Theorem 1 (finite time stability), p. 529: under Assumption 1, for every
`p > 0` there is a constant `C_{p,T}` such that every timestep function `h` satisfying
Assumption 2 with the fixed constants `α, β` makes `T` almost surely attainable
(`t_N ≥ T` for some finite `N`) and gives `E[sup_{0≤t≤T} ‖X̂_t‖^p] < C_{p,T}`. -/
theorem theorem_1 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α₁ β₁ : ℝ) (hA1 : Assumption1 f g α₁ β₁) (α β : ℝ)
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T) :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ h : SDEState m → ℝ, Assumption2 f h α β →
      (∀ᵐ ω ∂P, ∃ N : ℕ, T ≤ (grid f g h x0 W N ω).1) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖Xhat f g h x0 W t ω‖ₑ) ^ p ∂P
        < ENNReal.ofReal C := by sorry

end AdaptiveEM.Finite
