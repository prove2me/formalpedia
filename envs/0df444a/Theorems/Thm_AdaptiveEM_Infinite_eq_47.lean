-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_eq_47
-- name    : AdaptiveEM.Infinite.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:28.723051+00:00
-- url     : https://prove2.me/theorems/0950a2dc-f6e7-4c6e-9504-dc8b558350d1
-- title:
--   (47) — weighted partial-step energy inequality from $\underline t$ to $t$ (cross term corrected)
-- statement:
--   Let $f$, $g$, $h$ be as in the adaptive Euler–Maruyama scheme (5), started at $x_0$ and driven by a path $W$, with $h$ satisfying Assumption 8 (constants $h_{\max},\alpha,\beta$) and $\|g(x)\|^2\le\beta$ for all $x$. Fix $t\ge0$ and a path on which the grid passes $t$, i.e. $t<t_{n+1}$ for some $n$. With $\underline t$ the last grid time before $t$, $\overline X_t=\widehat X_{\underline t}$ and $\widehat X_t$ the continuous interpolant,
--   $$
--   e^{2\alpha t}\|\widehat X_t\|^2\le e^{2\alpha\underline t}\|\widehat X_{\underline t}\|^2+2e^{2\alpha(\underline t+h_{\max})}\beta(t-\underline t)+e^{2\alpha(\underline t+h_{\max})}\beta\|W_t-W_{\underline t}\|^2+2e^{2\alpha t}\big\langle\widehat X_{\underline t}+f(\widehat X_{\underline t})(t-\underline t),\,g(\widehat X_{\underline t})(W_t-W_{\underline t})\big\rangle.
--   $$
--
--   This is the partial-step counterpart of (45): together they bound $e^{2\alpha t}\|\widehat X_t\|^2$ at every time, not only at grid times.
--
--   **Correction to the printed statement.** The printed (47) has $\langle\phi(\widehat X_{\underline t}),\cdot\rangle$ with $\phi(x)=x+h(x)f(x)$ in the last term. Expanding $\|\widehat X_t\|^2$ gives the cross term $\langle\widehat X_{\underline t}+f(\widehat X_{\underline t})(t-\underline t),\cdot\rangle$ stated here, which is also the term the source uses when it sums (45) and (47) in (48) on the same page. As printed, the inequality fails in general.
--
--   **Formalization Note** The inequality is pathwise. The hypothesis that the grid passes $t$ is what makes $t-\underline t\le h(\widehat X_{\underline t})$, as the source uses; without it $\underline t$ carries a junk value.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 554, (46)–(47) (§6.3, proof of Theorem 5, Step 1), cross term as in (48)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 554, (47) (§6.3, proof of Theorem 5, Step 1), partial timestep from
`t̲` to `t`, with the cross term corrected: on every path whose AdaptiveEM.Finite.grid passes `t`
(some `t_{n+1} > t`), under (19) and `‖g‖² ≤ β` (18) with the same `β`,
`e^{2αt}‖X̂_t‖² ≤ e^{2αt̲}‖X̂_{t̲}‖² + 2e^{2α(t̲+h_max)}β(t − t̲) + e^{2α(t̲+h_max)}β‖W_t − W_{t̲}‖²
  + 2e^{2αt}⟨X̂_{t̲} + f(X̂_{t̲})(t − t̲), g(X̂_{t̲})(W_t − W_{t̲})⟩`.
The printed (47) has `φ(X̂_{t̲}) = X̂_{t̲} + h(X̂_{t̲}) f(X̂_{t̲})` in the cross term; the
expansion of `‖X̂_t‖²` (and the source's own (48)) gives `X̂_{t̲} + f(X̂_{t̲})(t − t̲)`. -/
theorem eq_47 {m d : ℕ} {Ω : Type*}
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (hmax α β : ℝ)
    (hA8 : Assumption8 f h hmax α β) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ β)
    (t : ℝ≥0) (ω : Ω) (hreach : ∃ n : ℕ, t < (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1) :
    Real.exp (2 * α * (t : ℝ)) * ‖AdaptiveEM.Finite.Xhat f g h x0 W t ω‖ ^ 2
      ≤ Real.exp (2 * α * (AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ)) * ‖AdaptiveEM.Finite.Xbar f g h x0 W t ω‖ ^ 2
        + 2 * Real.exp (2 * α * ((AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ) + hmax)) * β
            * ((t : ℝ) - AdaptiveEM.Finite.tlow f g h x0 W t ω)
        + Real.exp (2 * α * ((AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ) + hmax)) * β
            * ‖W t ω - W (AdaptiveEM.Finite.tlow f g h x0 W t ω) ω‖ ^ 2
        + 2 * Real.exp (2 * α * (t : ℝ))
            * inner ℝ (AdaptiveEM.Finite.Xbar f g h x0 W t ω
                + ((t : ℝ) - AdaptiveEM.Finite.tlow f g h x0 W t ω) • f (AdaptiveEM.Finite.Xbar f g h x0 W t ω))
              (AdaptiveEM.Finite.mulVec (g (AdaptiveEM.Finite.Xbar f g h x0 W t ω)) (W t ω - W (AdaptiveEM.Finite.tlow f g h x0 W t ω) ω)) := by sorry

end AdaptiveEM.Infinite
