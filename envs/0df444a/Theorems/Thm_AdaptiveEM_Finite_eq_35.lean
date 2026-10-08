-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_eq_35
-- name    : AdaptiveEM.Finite.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:26.16599+00:00
-- url     : https://prove2.me/theorems/f94da2de-0296-49fe-8685-a336de6435cf
-- title:
--   (35), p. 548 — one-step energy inequality of the K-scheme under condition (10)
-- statement:
--   Let $f$, $g$ and a timestep function $h$ satisfy Assumption 2 with constants $\alpha,\beta>0$, let $K>0$, and write $\varphi(x)=x+h(x)f(x)$. For every state $x\in\mathbb R^m$ and every Brownian increment $w\in\mathbb R^d$, one step of the K-scheme from $x$ with increment $w$ satisfies
--   $$\big\|P_K\big(x+h(x)f(x)+g(x)w\big)\big\|^2\le\|x\|^2+2\alpha\|x\|^2h(x)+2\beta h(x)+2\langle\varphi(x),g(x)w\rangle+\|g(x)w\|^2 .$$
--
--   Applied at $x=\widehat X^K_{t_n}$, $w=\Delta W_n$, this is the inequality (35) for $\|\widehat X^K_{t_{n+1}}\|^2$; summed over steps it gives the pathwise bound on which the moment estimates of Theorem 1 are built.
--
--   **Formalization Note** The inequality is stated for arbitrary $x$ and $w$, which is its content: the paper applies it pathwise to each step of (34). $K>0$ corresponds to the paper's $K>\|X_0\|$.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 548, §6.1, proof of Theorem 1, Step 2, (35)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Finite_KScheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), §6.1, proof of Theorem 1, Step 2, (35), p. 548: one step of the K-scheme
(34) from the state `x` with Brownian increment `w`, under Assumption 2, satisfies
`‖P_K(x + h(x) f(x) + g(x) w)‖² ≤ ‖x‖² + 2α‖x‖² h(x) + 2β h(x) + 2⟨φ(x), g(x) w⟩ + ‖g(x) w‖²`,
`φ(x) = x + h(x) f(x)`. Stated for every `x` and `w` (the step is applied pathwise). -/
theorem eq_35 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (α β : ℝ) (hA2 : Assumption2 f h α β) (K : ℝ) (hK : 0 < K)
    (x : SDEState m) (w : SDEState d) :
    ‖PK K (x + h x • f x + mulVec (g x) w)‖ ^ 2 ≤
      ‖x‖ ^ 2 + 2 * α * ‖x‖ ^ 2 * h x + 2 * β * h x
        + 2 * ⟪x + h x • f x, mulVec (g x) w⟫ + ‖mulVec (g x) w‖ ^ 2 := by sorry

end AdaptiveEM.Finite
