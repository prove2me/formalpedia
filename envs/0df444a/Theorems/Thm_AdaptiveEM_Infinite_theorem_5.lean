-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_theorem_5
-- name    : AdaptiveEM.Infinite.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:51.819099+00:00
-- url     : https://prove2.me/theorems/2184295b-5c31-455e-9953-480731d10af5
-- title:
--   Theorem 5 (Stability in infinite interval) — $\mathbb E\|\widehat X_t\|^p,\ \mathbb E\|\overline X_t\|^p<C_p$ for all $t\ge0$
-- statement:
--   Let $W$ be a $d$-dimensional $(\mathcal F_t)$-Brownian motion on a probability space, fix $x_0\in\mathbb R^m$, the constants $\alpha_7,\beta_7$ of Assumption 7 and constants $h_{\max},\alpha,\beta$. Then for every $p\in(0,\infty)$ there is a constant $C_p$ such that for all $f,g$ satisfying Assumption 7 with constants $\alpha_7,\beta_7$ and every timestep function $h$ satisfying Assumption 8 with constants $h_{\max},\alpha,\beta$, the interpolants $\widehat X$, $\overline X$ of the adaptive Euler–Maruyama scheme from $x_0$ satisfy
--   $$\mathbb E\big[\|\widehat X_t\|^p\big]<C_p,\qquad \mathbb E\big[\|\overline X_t\|^p\big]<C_p\qquad\text{for all }t\ge0.$$
--
--   This is the discrete counterpart of Lemma 3: with a timestep that respects the dissipative structure (19), the numerical solution inherits time-uniform moment bounds. Because the constant does not depend on $h$, it applies at once to every refined timestep $h^\delta\le h$, which is how it enters the proof of Theorem 6.
--
--   **Formalization Note** Moments are lower Lebesgue integrals in $[0,\infty]$. The source says $C_p$ depends solely on $p$, $x_0$, $h_{\max}$ and the constants $\alpha,\beta$ of Assumption 8; accordingly the constant is chosen after $p$, $x_0$, $h_{\max}$, $\alpha$, $\beta$ and before $f$, $g$, $h$ and $t$. It may also depend on $\beta_7$, the bound of $\|g\|^2$ in (18), which the source's proof identifies with $\beta$ (and, harmlessly, on $\alpha_7$).
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 533, Theorem 5

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 533, Theorem 5 (stability in infinite interval): if `f, g` satisfy
Assumption 7 with constants `α₇, β₇`, then for every `p > 0` there is `C_p` such that for
every such `f, g`, every timestep function `h` satisfying Assumption 8 with the given
`h_max, α, β` and every `t ≥ 0`, `E‖X̂_t‖^p < C_p` and `E‖X̄_t‖^p < C_p`. The constant depends
only on `p`, `x0`, `h_max`, `α`, `β` (and on the bound `β₇` of `‖g‖²`, which the source's proof
identifies with `β`); not on `f`, `g`, `h` or `t`.
Moments are lower Lebesgue integrals in `[0, ∞]`. -/
theorem theorem_5 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsWienerMartingale P ℱ W)
    (x0 : SDEState m) (α₇ β₇ : ℝ) (hmax α β : ℝ) :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ,
      ∀ (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d), Assumption7 f g α₇ β₇ →
      ∀ h : SDEState m → ℝ, Assumption8 f h hmax α β →
      ∀ t : ℝ≥0,
        ∫⁻ ω, ‖AdaptiveEM.Finite.Xhat f g h x0 W t ω‖ₑ ^ p ∂P < ENNReal.ofReal C ∧
        ∫⁻ ω, ‖AdaptiveEM.Finite.Xbar f g h x0 W t ω‖ₑ ^ p ∂P < ENNReal.ofReal C := by sorry

end AdaptiveEM.Infinite
