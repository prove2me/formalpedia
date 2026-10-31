-- Prove2me | Theorems.Thm_DynTargetMV_eq_C_15_C_16
-- name    : DynTargetMV.eq_C_15_C_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:43.986375+00:00
-- url     : https://prove2.me/theorems/774abde9-c147-4dc1-8651-a32c1b9d17c6
-- title:
--   (C.15), (C.16) — mean and variance for wealth-independent strategies
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let $t\in[0,T)$, $x\in\mathbb R$, $\varepsilon\in(0,T-t)$, $\pi\in\mathbb R^m$, and let $\hat\pi(s)$ be right-continuous and square-integrable on $[0,T)$. Then the wealth equation of $\pi_{t,\varepsilon,\pi}$ from $(t,x)$ has a unique strong solution with square-integrable terminal value, and
--   $$
--   E_t[X^{\pi_{t,\varepsilon,\pi}}(T)]=e^{\int_t^Tr(s)ds}\Bigl\{x+\int_{t+\varepsilon}^Te^{-\int_t^sr(z)dz}b(s)^\top\hat\pi(s)ds+\int_t^{t+\varepsilon}e^{-\int_t^sr(z)dz}b(s)^\top\pi\,ds\Bigr\},
--   $$
--   $$
--   \operatorname{var}_t(X^{\pi_{t,\varepsilon,\pi}}(T))=e^{2\int_t^Tr(s)ds}\Bigl\{\int_{t+\varepsilon}^Te^{-2\int_t^sr(z)dz}\|\sigma(s)^\top\hat\pi(s)\|^2ds+\int_t^{t+\varepsilon}e^{-2\int_t^sr(z)dz}\|\sigma(s)^\top\pi\|^2ds\Bigr\}.
--   $$
--   These closed forms start the first-order analysis for target (2.8).
--
--   Differences from the source:
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - generalization: x ∈ 𝕏_t for a feasible π̂ → any x ∈ ℝ, without feasibility of π̂; reason: the computation uses neither feasibility nor reachability, and the source's case is an instance
--   - encoding: the formulas take the solution and its moments for granted → the conclusion asserts a unique solution with L² terminal value; reason: so that the integral and the variance are not junk values
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.15), (C.16), p.28

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_RightContSqInt
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
import Definitions.Def_DynTargetMV_IsStdBM

open MeasureTheory ProbabilityTheory Set Matrix

namespace DynTargetMV

/-- (C.15), (C.16): mean and variance of the terminal wealth of the spike `π_{t,ε,π}` around a wealth-
independent strategy `π̂(s,y) = p(s)`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.15), (C.16), p.28.

**Formalization Note** The formulas hold from every `x ∈ ℝ`. The conclusion includes the existence and
uniqueness of the solution from `(t,x)` and its `L²` terminal value. -/
theorem eq_C_15_C_16 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {t ε : ℝ} (ht : t ∈ Ico 0 M.T) (x : ℝ) (hε : ε ∈ Ioo 0 (M.T - t))
    {p : ℝ → Fin m → ℝ} (hp : M.RightContSqInt p) (π : Fin m → ℝ) :
    ∃ X : ℝ → Ω → ℝ,
      M.IsUniqueWealthFrom P F W (spike t ε (fun _ _ => π) (fun s _ => p s)) t x X ∧
      MemLp (X M.T) 2 P ∧
      (∫ ω, X M.T ω ∂P) = Real.exp (∫ s in t..M.T, M.r s) *
        (x + (∫ s in (t + ε)..M.T, Real.exp (-∫ z in t..s, M.r z) * (M.b s ⬝ᵥ p s)) +
          ∫ s in t..(t + ε), Real.exp (-∫ z in t..s, M.r z) * (M.b s ⬝ᵥ π)) ∧
      variance (X M.T) P = Real.exp (2 * ∫ s in t..M.T, M.r s) *
        ((∫ s in (t + ε)..M.T, Real.exp (-2 * ∫ z in t..s, M.r z) * sqNorm ((M.σ s)ᵀ *ᵥ p s)) +
          ∫ s in t..(t + ε), Real.exp (-2 * ∫ z in t..s, M.r z) * sqNorm ((M.σ s)ᵀ *ᵥ π)) := by sorry

end DynTargetMV
