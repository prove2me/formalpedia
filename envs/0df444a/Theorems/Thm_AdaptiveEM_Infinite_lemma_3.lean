-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_lemma_3
-- name    : AdaptiveEM.Infinite.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:56.26099+00:00
-- url     : https://prove2.me/theorems/3b881b9a-12cf-42bd-b2a7-299f07e28dc7
-- title:
--   Lemma 3 (SDE stability in infinite time interval) — $\sup_{t\ge0}\mathbb E\|X_t\|^p<\infty$ under Assumption 7
-- statement:
--   Let $W$ be a $d$-dimensional standard Brownian motion with respect to a filtration $(\mathcal F_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$. Suppose $f:\mathbb R^m\to\mathbb R^m$ and $g:\mathbb R^m\to\mathbb R^{m\times d}$ satisfy Assumption 7 (local Lipschitz continuity (7), the dissipative condition $\langle x,f(x)\rangle\le-\alpha\|x\|^2+\beta$ and the bound $\|g(x)\|^2\le\beta$), and let $X$ be a solution of
--   $$\mathrm dX_t=f(X_t)\,\mathrm dt+g(X_t)\,\mathrm dW_t,\qquad X_0=x_0,$$
--   on $[0,\infty)$. Then for every $p\in(0,\infty)$ there is a constant $C_p$ such that
--   $$\mathbb E\big[\|X_t\|^p\big]\le C_p\qquad\text{for all }t\ge0.$$
--
--   The bound is uniform in time: the dissipative drift keeps every moment of the solution bounded on the whole half-line. It controls the moments of the exact solution that enter the time-uniform error analysis of the scheme.
--
--   **Formalization Note** A solution on $[0,\infty)$ is a process that solves the SDE on every horizon $[0,T]$. The moment is a lower Lebesgue integral with values in $[0,\infty]$, so the statement asserts finiteness. The constant comes after $f$, $g$, $x_0$ and the solution, and before $t$; the source says it depends only on $x_0$ and $p$, with $f,g$ fixed.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 532, Lemma 3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 532, Lemma 3 (SDE stability in infinite time interval): if `f, g`
satisfy Assumption 7 and `X` solves `dX_t = f(X_t) dt + g(X_t) dW_t`, `X_0 = x0`, on every
horizon `[0, T]`, then for every `p > 0` there is `C_p` with `E‖X_t‖^p ≤ C_p` for all
`t ≥ 0`. The moment is a lower Lebesgue integral in `[0, ∞]`. -/
theorem lemma_3 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (x0 : SDEState m)
    (α₇ β₇ : ℝ) (hA7 : Assumption7 f g α₇ β₇)
    (X : ℝ≥0 → Ω → SDEState m)
    (hX : ∀ T : ℝ≥0, IsSolution P ℱ W T (fun _ => x0) (fun z => f z.2) (fun z => g z.2) X) :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ t : ℝ≥0, ∫⁻ ω, ‖X t ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal C := by sorry

end AdaptiveEM.Infinite
