-- Prove2me | Theorems.Thm_DynTargetMV_eq_C_3_C_4
-- name    : DynTargetMV.eq_C_3_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:13.929998+00:00
-- url     : https://prove2.me/theorems/fbb7e575-15ef-4a0c-8c0f-3cd7f2b9799e
-- title:
--   (C.3), (C.4) — mean and variance of the wealth-proportional spike
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let $t\in[0,T)$, $x>0$, $\varepsilon\in(0,T-t)$, $\pi\in\mathbb R^m$, and let $\hat u$ be right-continuous and square-integrable on $[0,T)$. Consider the strategy $\pi'_{t,\varepsilon,\pi}$ of (C.1), which invests $(\pi/x)y$ for $s\in[t,t+\varepsilon)$ and $y\hat u(s)$ otherwise. Then the wealth equation from $(t,x)$ has a unique strong solution $X$ with square-integrable terminal value, and
--   $$
--   E_t[X(T)]=x\,e^{\int_t^T(r(s)+b(s)^\top\hat u(s))ds}\,e^{\int_t^{t+\varepsilon}(b(s)^\top\pi/x-b(s)^\top\hat u(s))ds},
--   $$
--   $$
--   \operatorname{var}_t[X(T)]=x^2e^{2\int_t^T(r(s)+b(s)^\top\hat u(s))ds}\,e^{2\int_t^{t+\varepsilon}(b(s)^\top\pi/x-b(s)^\top\hat u(s))ds}\Bigl[e^{\int_t^{t+\varepsilon}(\|\sigma(s)^\top\pi/x\|^2-\|\sigma(s)^\top\hat u(s)\|^2)ds}\,e^{\int_t^T\|\sigma(s)^\top\hat u(s)\|^2ds}-1\Bigr].
--   $$
--   These closed forms start the first-order analysis for target (2.7).
--
--   Differences from the source:
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - generalization: t ∈ [0,T), x ∈ 𝕏_t for a feasible π̂ → any x > 0, without feasibility of π̂; reason: the computation uses neither feasibility nor reachability, and the source's case is an instance
--   - encoding: the formulas take the solution and its moments for granted → the conclusion asserts a unique solution with L² terminal value; reason: so that the integral and the variance are not junk values
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.1), (C.3), (C.4), p.26

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_RightContSqInt
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
import Definitions.Def_DynTargetMV_IsStdBM

open MeasureTheory ProbabilityTheory Set Matrix

namespace DynTargetMV

/-- (C.3), (C.4): mean and variance of the terminal wealth under the strategy `π′_{t,ε,π}` of (C.1), which
invests `(π/x)y` on `[t,t+ε)` and `π̂(s,y) = yû(s)` otherwise. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.1), (C.3), (C.4), p.26.

**Formalization Note** The conclusion includes the existence and uniqueness of the solution from
`(t,x)` and its `L²` terminal value, so the formulas are not vacuous and the integral and variance are
not junk values. -/
theorem eq_C_3_C_4 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {t x ε : ℝ} (ht : t ∈ Ico 0 M.T) (hx : 0 < x) (hε : ε ∈ Ioo 0 (M.T - t))
    {û : ℝ → Fin m → ℝ} (hû : M.RightContSqInt û) (π : Fin m → ℝ) :
    ∃ X : ℝ → Ω → ℝ,
      M.IsUniqueWealthFrom P F W
        (spike t ε (fun _ y => y • ((1 / x) • π)) (fun s y => y • û s)) t x X ∧
      MemLp (X M.T) 2 P ∧
      (∫ ω, X M.T ω ∂P) =
        x * Real.exp (∫ s in t..M.T, (M.r s + M.b s ⬝ᵥ û s)) *
          Real.exp (∫ s in t..(t + ε), (M.b s ⬝ᵥ ((1 / x) • π) - M.b s ⬝ᵥ û s)) ∧
      variance (X M.T) P =
        x ^ 2 * Real.exp (2 * ∫ s in t..M.T, (M.r s + M.b s ⬝ᵥ û s)) *
          Real.exp (2 * ∫ s in t..(t + ε), (M.b s ⬝ᵥ ((1 / x) • π) - M.b s ⬝ᵥ û s)) *
          (Real.exp (∫ s in t..(t + ε),
              (sqNorm ((M.σ s)ᵀ *ᵥ ((1 / x) • π)) - sqNorm ((M.σ s)ᵀ *ᵥ û s))) *
            Real.exp (∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ û s)) - 1) := by sorry

end DynTargetMV
