-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_eq_45
-- name    : AdaptiveEM.Infinite.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:10.528995+00:00
-- url     : https://prove2.me/theorems/100a6fa6-873f-40a4-a0e4-4c72ed474722
-- title:
--   (45) — weighted one-step energy inequality $e^{2\alpha t_{n+1}}\|\widehat X_{t_{n+1}}\|^2\le\dots$ for the adaptive scheme
-- statement:
--   Let $f$, $g$, $h$ be as in the adaptive Euler–Maruyama scheme (5), started at $x_0$ and driven by a path $W$. Assume $h$ satisfies Assumption 8 with constants $h_{\max},\alpha,\beta$ (so $0<h\le h_{\max}$ and $\langle x,f(x)\rangle+\frac12h(x)\|f(x)\|^2\le-\alpha\|x\|^2+\beta$), and that $\|g(x)\|^2\le\beta$ for all $x$ with the same $\beta$. Write $\phi(x)=x+h(x)f(x)$, $h_n=h(\widehat X_{t_n})$ and $\Delta W_n=W_{t_{n+1}}-W_{t_n}$. Then along every path and for every $n\ge0$,
--   $$
--   e^{2\alpha t_{n+1}}\|\widehat X_{t_{n+1}}\|^2\le e^{2\alpha t_n}\|\widehat X_{t_n}\|^2+2e^{2\alpha(t_n+h_{\max})}\beta h_n+e^{2\alpha(t_n+h_{\max})}\beta\|\Delta W_n\|^2+2e^{2\alpha t_{n+1}}\langle\phi(\widehat X_{t_n}),g(\widehat X_{t_n})\Delta W_n\rangle.
--   $$
--
--   This is the discrete energy estimate of one step of the scheme. The weight $e^{2\alpha t}$ absorbs the dissipation, so that summing over steps gives a bound on $e^{2\alpha t}\|\widehat X_t\|^2$ that is uniform after dividing by the weight; it is the first step of the proof of the time-uniform stability theorem.
--
--   **Formalization Note** The inequality is pathwise and deterministic: $W$ is any path, $t_n$ and $\widehat X_{t_n}$ are the components of `grid n ω`.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 554, (45) (§6.3, proof of Theorem 5, Step 1; φ defined on p. 553)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 554, (45) (§6.3, proof of Theorem 5, Step 1): along every path of
the adaptive scheme (5), with `φ(x) = x + h(x) f(x)`, `h_n = h(X̂_{t_n})` and
`ΔW_n = W_{t_{n+1}} − W_{t_n}`, under (19) and `‖g‖² ≤ β` (18) with the same `β`:
`e^{2αt_{n+1}}‖X̂_{t_{n+1}}‖² ≤ e^{2αt_n}‖X̂_{t_n}‖² + 2e^{2α(t_n+h_max)}βh_n
  + e^{2α(t_n+h_max)}β‖ΔW_n‖² + 2e^{2αt_{n+1}}⟨φ(X̂_{t_n}), g(X̂_{t_n})ΔW_n⟩`. -/
theorem eq_45 {m d : ℕ} {Ω : Type*}
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (hmax α β : ℝ)
    (hA8 : Assumption8 f h hmax α β) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ β)
    (n : ℕ) (ω : Ω) :
    Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 : ℝ)) * ‖(AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).2‖ ^ 2
      ≤ Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ)) * ‖(AdaptiveEM.Finite.grid f g h x0 W n ω).2‖ ^ 2
        + 2 * Real.exp (2 * α * (((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ) + hmax)) * β
            * h (AdaptiveEM.Finite.grid f g h x0 W n ω).2
        + Real.exp (2 * α * (((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ) + hmax)) * β
            * ‖W (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 ω - W (AdaptiveEM.Finite.grid f g h x0 W n ω).1 ω‖ ^ 2
        + 2 * Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 : ℝ))
            * inner ℝ ((AdaptiveEM.Finite.grid f g h x0 W n ω).2
                + h (AdaptiveEM.Finite.grid f g h x0 W n ω).2 • f (AdaptiveEM.Finite.grid f g h x0 W n ω).2)
              (AdaptiveEM.Finite.mulVec (g (AdaptiveEM.Finite.grid f g h x0 W n ω).2)
                (W (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 ω - W (AdaptiveEM.Finite.grid f g h x0 W n ω).1 ω)) := by sorry

end AdaptiveEM.Infinite
