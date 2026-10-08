-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_eq_37
-- name    : AdaptiveEM.Finite.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:54.776461+00:00
-- url     : https://prove2.me/theorems/7c8c39c8-c48a-4573-8b8e-944d3203659e
-- title:
--   (37), p. 548 — partial-step energy inequality of the K-scheme for t − t̲ ≤ h
-- statement:
--   Let $f$, $g$ and a timestep function $h$ satisfy Assumption 2 with constants $\alpha,\beta>0$, and let $K>0$. For every state $x\in\mathbb R^m$, every increment $w\in\mathbb R^d$ and every $\tau$ with $0\le\tau\le h(x)$,
--   $$\big\|P_K\big(x+\tau f(x)+g(x)w\big)\big\|^2\le\|x\|^2+2\alpha\|x\|^2\tau+2\beta\tau+2\langle x+\tau f(x),g(x)w\rangle+\|g(x)w\|^2 .$$
--
--   Applied at $x=\widehat X^K_{\underline t}$, $\tau=t-\underline t$, $w=W_t-W_{\underline t}$, this is the inequality (37) for the continuous K-scheme approximation $\|\widehat X^K_t\|^2$ between grid times; together with (35) it gives a pathwise bound valid at every time.
--
--   **Formalization Note** Stated for arbitrary $x$, $w$ and $\tau\in[0,h(x)]$, the role of $t-\underline t\le h_{n_t}$; the paper applies it pathwise. $K>0$ corresponds to the paper's $K>\|X_0\|$.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 548, §6.1, proof of Theorem 1, Step 2, (37)

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

/-- Fang–Giles (2020), §6.1, proof of Theorem 1, Step 2, (37), p. 548: the partial K-scheme step
of length `τ = t - t̲ ∈ [0, h(x)]` from the state `x` with Brownian increment `w` satisfies
`‖P_K(x + τ f(x) + g(x) w)‖² ≤ ‖x‖² + 2α‖x‖² τ + 2β τ + 2⟨x + τ f(x), g(x) w⟩ + ‖g(x) w‖²`. -/
theorem eq_37 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (α β : ℝ) (hA2 : Assumption2 f h α β) (K : ℝ) (hK : 0 < K)
    (x : SDEState m) (w : SDEState d) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτh : τ ≤ h x) :
    ‖PK K (x + τ • f x + mulVec (g x) w)‖ ^ 2 ≤
      ‖x‖ ^ 2 + 2 * α * ‖x‖ ^ 2 * τ + 2 * β * τ
        + 2 * ⟪x + τ • f x, mulVec (g x) w⟫ + ‖mulVec (g x) w‖ ^ 2 := by sorry

end AdaptiveEM.Finite
