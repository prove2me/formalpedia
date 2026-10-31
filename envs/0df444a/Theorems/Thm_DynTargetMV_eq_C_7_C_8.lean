-- Prove2me | Theorems.Thm_DynTargetMV_eq_C_7_C_8
-- name    : DynTargetMV.eq_C_7_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:51.330413+00:00
-- url     : https://prove2.me/theorems/37d43376-83e2-4f7f-9781-bbe6c3adc65c
-- title:
--   (C.7), (C.8) — first-order limits for target (2.7)
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let $t\in[0,T)$, $x>0$, $\pi\in\mathbb R^m$, let $\hat u$ be right-continuous and square-integrable on $[0,T)$, and $\hat\pi(s,y)=y\hat u(s)$. Then
--   $$
--   \lim_{\varepsilon\downarrow0}\frac{E_t[X^{\pi_{t,\varepsilon,\pi}}(T)]-E_t[X^{\hat\pi}(T)]}\varepsilon=x\,e^{\int_t^T(r(s)+b(s)^\top\hat u(s))ds}\bigl(b(t)^\top\pi/x-b(t)^\top\hat u(t)\bigr),
--   $$
--   $$
--   \lim_{\varepsilon\downarrow0}\frac{\operatorname{var}_t(X^{\pi_{t,\varepsilon,\pi}}(T))-\operatorname{var}_t(X^{\hat\pi}(T))}\varepsilon=2x^2e^{2\int_t^T(r(s)+b(s)^\top\hat u(s))ds}\,e^{\int_t^T\|\sigma(s)^\top\hat u(s)\|^2ds}
--   $$
--   $$
--   \times\Bigl[\tfrac12\bigl(\|\sigma(t)^\top\pi/x\|^2-\|\sigma(t)^\top\hat u(t)\|^2\bigr)+\bigl(1-e^{-\int_t^T\|\sigma(s)^\top\hat u(s)\|^2ds}\bigr)\bigl(b(t)^\top\pi/x-b(t)^\top\hat u(t)\bigr)\Bigr].
--   $$
--   These limits turn the conditions of Definition 1 into a pointwise quadratic program.
--
--   Differences from the source:
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - generalization: t ∈ [0,T), x ∈ 𝕏_t for a feasible π̂ → any x > 0, without feasibility of π̂; reason: the computation uses neither feasibility nor reachability, and the source's case is an instance
--   - encoding: the limits take the solutions and their moments for granted → the conclusion asserts unique solutions with L² terminal values for π̂ and for every ε ∈ (0,T−t); reason: so that the integrals and the variances are not junk values
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.7), (C.8), p.26

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_RightContSqInt
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
import Definitions.Def_DynTargetMV_IsStdBM

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology

namespace DynTargetMV

/-- (C.7), (C.8): the first-order limits, as `ε ↓ 0`, of the mean and variance of the terminal wealth
of the spike `π_{t,ε,π}` of (2.4) around `π̂(s,y) = yû(s)`, from `(t,x)` with `x > 0`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.7), (C.8), p.26.

**Formalization Note** The solutions are asserted to exist, be unique and have `L²` terminal values,
for every `ε ∈ (0,T−t)`. -/
theorem eq_C_7_C_8 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {t x : ℝ} (ht : t ∈ Ico 0 M.T) (hx : 0 < x)
    {û : ℝ → Fin m → ℝ} (hû : M.RightContSqInt û) (π : Fin m → ℝ) :
    ∃ (Xh : ℝ → Ω → ℝ) (Xε : ℝ → ℝ → Ω → ℝ),
      M.IsUniqueWealthFrom P F W (fun s y => y • û s) t x Xh ∧ MemLp (Xh M.T) 2 P ∧
      (∀ ε ∈ Ioo 0 (M.T - t),
        M.IsUniqueWealthFrom P F W (spike t ε (fun _ _ => π) (fun s y => y • û s)) t x (Xε ε) ∧
          MemLp (Xε ε M.T) 2 P) ∧
      Tendsto (fun ε => ((∫ ω, Xε ε M.T ω ∂P) - ∫ ω, Xh M.T ω ∂P) / ε) (𝓝[>] 0)
        (𝓝 (x * Real.exp (∫ s in t..M.T, (M.r s + M.b s ⬝ᵥ û s)) *
          (M.b t ⬝ᵥ ((1 / x) • π) - M.b t ⬝ᵥ û t))) ∧
      Tendsto (fun ε => (variance (Xε ε M.T) P - variance (Xh M.T) P) / ε) (𝓝[>] 0)
        (𝓝 (2 * x ^ 2 * Real.exp (2 * ∫ s in t..M.T, (M.r s + M.b s ⬝ᵥ û s)) *
          Real.exp (∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ û s)) *
          ((1 / 2) * (sqNorm ((M.σ t)ᵀ *ᵥ ((1 / x) • π)) - sqNorm ((M.σ t)ᵀ *ᵥ û t)) +
            (1 - Real.exp (-∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ û s))) *
              (M.b t ⬝ᵥ ((1 / x) • π) - M.b t ⬝ᵥ û t)))) := by sorry

end DynTargetMV
