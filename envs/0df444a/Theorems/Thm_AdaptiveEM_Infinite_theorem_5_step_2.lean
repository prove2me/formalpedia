-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_theorem_5_step_2
-- name    : AdaptiveEM.Infinite.theorem_5_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:48.370515+00:00
-- url     : https://prove2.me/theorems/b125a0f0-c4f2-4234-a398-aac0efb7f093
-- title:
--   §6.3 Step 2 — $\mathbb E[\widehat M^{\alpha,p}_t]\le 2C^4_p\|x_0\|^p+2C^5_pe^{\alpha pt}$, uniformly in $h$
-- statement:
--   Let $W$ be a $d$-dimensional $(\mathcal F_t)$-Brownian motion on a probability space, and fix the constants $\alpha_7,\beta_7$ of Assumption 7 and $h_{\max},\alpha,\beta$ of Assumption 8. For a timestep function $h$ let $\widehat X$ be the continuous interpolant of the adaptive Euler–Maruyama scheme started at $x_0$ and define
--   $$\widehat M^{\alpha,p}_t=\sup_{0\le s\le t}e^{\alpha ps}\|\widehat X_s\|^p.$$
--   Then for every $p\ge4$ there are constants $C^4_p$ and $C^5_p$, independent of the coefficients and of the initial value, such that for all $f,g$ satisfying Assumption 7 with constants $\alpha_7,\beta_7$, every $x_0\in\mathbb R^m$, every $h$ satisfying Assumption 8 with constants $h_{\max},\alpha,\beta$ and every $t\ge0$,
--   $$\mathbb E\big[\widehat M^{\alpha,p}_t\big]\le 2C^4_p\|x_0\|^p+2C^5_pe^{\alpha pt}.$$
--
--   Dividing by $e^{\alpha pt}$ shows that $\mathbb E\|\widehat X_t\|^p$ is bounded uniformly in $t$; this is the core estimate of the time-uniform stability theorem (Theorem 5), and its constants do not depend on the particular timestep function.
--
--   **Formalization Note** The supremum and the expectation are taken in $[0,\infty]$. The constants are chosen after $p$, $h_{\max}$, $\alpha$, $\beta$ (and $\alpha_7,\beta_7$) and before $f$, $g$, $x_0$, $h$ and $t$: the bound's form $C^4_p\|x_0\|^p+C^5_pe^{\alpha pt}$ and the proof (pp. 555–556) show that $C^4_p,C^5_p$ involve only $p$, $h_{\max}$, $\alpha$ and the bound $\beta$ that the source uses for both (18) and (19); here the bound $\beta_7$ of $\|g\|^2$ is kept separate, so the constants may depend on it. $\alpha$ is the constant of Assumption 8. The source proves the estimate for $p\ge4$ and obtains smaller $p$ afterwards by Hölder's inequality.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 556, §6.3, proof of Theorem 5, end of Step 2 (M̂ defined on p. 553)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 556, §6.3, proof of Theorem 5, end of Step 2: with
`M̂^{α,p}_t = sup_{0≤s≤t} e^{αps}‖X̂_s‖^p` (p. 553): for every `p ≥ 4` there are constants
`C⁴_p, C⁵_p` (depending on `p`, `h_max`, `α`, `β` and the bound `β₇` of `‖g‖²`) such that for
all `f, g` satisfying Assumption 7 with constants `α₇, β₇`, every initial value `x0`, every
timestep function `h` satisfying Assumption 8 with the given `h_max, α, β` and every `t ≥ 0`,
`E[M̂^{α,p}_t] ≤ 2C⁴_p‖x0‖^p + 2C⁵_p e^{αpt}`. Expectation and supremum are taken in `[0, ∞]`. -/
theorem theorem_5_step_2 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsWienerMartingale P ℱ W)
    (α₇ β₇ : ℝ) (hmax α β : ℝ) :
    ∀ p : ℝ, 4 ≤ p → ∃ C4 C5 : ℝ,
      ∀ (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d), Assumption7 f g α₇ β₇ →
      ∀ x0 : SDEState m, ∀ h : SDEState m → ℝ,
      Assumption8 f h hmax α β →
      ∀ t : ℝ≥0,
        ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ≥0) t,
            ENNReal.ofReal (Real.exp (α * p * (s : ℝ))) * ‖AdaptiveEM.Finite.Xhat f g h x0 W s ω‖ₑ ^ p) ∂P
          ≤ ENNReal.ofReal (2 * C4 * ‖x0‖ ^ p + 2 * C5 * Real.exp (α * p * (t : ℝ))) := by sorry

end AdaptiveEM.Infinite
