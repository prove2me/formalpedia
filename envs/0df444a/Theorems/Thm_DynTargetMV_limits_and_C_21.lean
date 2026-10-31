-- Prove2me | Theorems.Thm_DynTargetMV_limits_and_C_21
-- name    : DynTargetMV.limits_and_C_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:30.907068+00:00
-- url     : https://prove2.me/theorems/4863e7e2-8c7c-4d7c-8a76-a35c427791f1
-- title:
--   p.29, (C.21) — first-order limits for target (2.9), and $\bar H\ge0$ (corrected: $\sigma(t)$ in the bracket; $\xi>x_0e^{\int r}$ for (C.21))
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let Assumption 3 hold, let $L$ be the target (2.9), let $\hat v$ be right-continuous and square-integrable on $[0,T)$, and $\hat\pi(s,y)=\hat v(s)(x^*(s)-y)$. For $t\in[0,T)$, $x<x^*(t)$, $\pi\in\mathbb R^m$ and $v:=\pi/(x^*(t)-x)$,
--   $$
--   \lim_{\varepsilon\downarrow0}\frac{E_t[X^{\pi_{t,\varepsilon,\pi}}(T)]-E_t[X^{\hat\pi}(T)]}\varepsilon=(x^*(t)-x)e^{\int_t^T(r(s)-b(s)^\top\hat v(s))ds}\bigl(b(t)^\top v-b(t)^\top\hat v(t)\bigr),
--   $$
--   $$
--   \lim_{\varepsilon\downarrow0}\frac{\operatorname{var}_t(X^{\pi_{t,\varepsilon,\pi}}(T))-\operatorname{var}_t(X^{\hat\pi}(T))}\varepsilon=2(x^*(t)-x)^2e^{2\int_t^T(r(s)-b(s)^\top\hat v(s))ds}e^{\int_t^T\|\sigma(s)^\top\hat v(s)\|^2ds}
--   $$
--   $$
--   \times\Bigl[\tfrac12\bigl(\|\sigma(t)^\top v\|^2-\|\sigma(t)^\top\hat v(t)\|^2\bigr)-\bigl(1-e^{-\int_t^T\|\sigma(s)^\top\hat v(s)\|^2ds}\bigr)\bigl(b(t)^\top v-b(t)^\top\hat v(t)\bigr)\Bigr].
--   $$
--   For such $(t,x)$, the target $E_t[X^{\hat\pi}(T)]\ge L(t,x)$ holds if and only if $\bar H(t;\hat v)\ge0$. If moreover $\hat\pi$ is feasible and $\xi>x_0e^{\int_0^Tr(s)ds}$, then
--   $$
--   \bar H(t;\hat v)=\int_t^Tb(s)^\top\hat v(s)ds-\int_t^T\psi(s)ds\ge0,\quad t\in[0,T). \tag{C.21}
--   $$
--   These are the inputs of the characterization (C.22).
--
--   Differences from the source:
--   - correction: the bracket of the second limit has σ(s)⊤v and σ(s)⊤v̂(s) → σ(t)⊤v and σ(t)⊤v̂(t); reason: s is not a free variable there, and the limit of the variance quotient at time t has σ(t), compare (C.8), and the derivation from it with u = −v
--   - correction: "because π̂ is feasible ..." gives (C.21) for every ξ ≥ x₀e^{∫₀ᵀ r} → (C.21) from feasibility assumes ξ > x₀e^{∫₀ᵀ r}; the equivalence is stated for each x < x*(t); reason: at equality X ≡ x*, 𝕏_t = {x*(t)}, and the target is met whatever H̄ is, so feasibility gives nothing
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - encoding: a feedback strategy is a measurable function on [0,T)×ℝ → a total function ℝ → ℝ → ℝ^m with measurability asked on [0,T)×ℝ only; reason: its values outside [0,T)×ℝ are never used
--   - generalization: x ∈ 𝕏_t with x < x*(t), for a feasible π̂ → any x < x*(t), without feasibility of π̂, for the limits and the equivalence; reason: the computation uses neither feasibility nor reachability, and the source's case is an instance
--   - encoding: the limits take the solutions and their moments for granted → the conclusion asserts unique solutions with L² terminal values for π̂ and for every ε ∈ (0,T−t); reason: so that the integrals and the variances are not junk values
--   - encoding: Qπ(s,X(s)) ≥ 0, s ∈ [t,T), in feasibility → a.s., for all s ∈ [0,T) simultaneously; reason: the pathwise reading of the printed constraint
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.29, (C.21)

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_spike
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_RightContSqInt
import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom
import Definitions.Def_DynTargetMV_IsStdBM
import Definitions.Def_DynTargetMV_Market_Assumption3
import Definitions.Def_DynTargetMV_Market_Feasible
import Definitions.Def_DynTargetMV_Market_targetAspiration
import Definitions.Def_DynTargetMV_Market_xStar
import Definitions.Def_DynTargetMV_Market_Hbar

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology

namespace DynTargetMV

/-- The first-order limits for target (2.9), and (C.21). For `π̂(s,y) = v̂(s)(x*(s) − y)` and `x < x*(t)`,
`v := π/(x*(t) − x)`, the mean and variance of the terminal wealth of `π_{t,ε,π}` have the printed
first-order limits, `E_t[X^π̂(T)] ≥ L(t,x)` is equivalent to `H̄(t;v̂) ≥ 0`, and if `π̂` is feasible and
`ξ > x₀e^{∫₀ᵀ r}` then `H̄(t;v̂) ≥ 0` on `[0,T)`, (C.21). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.29, (C.21).

**Formalization Note** The bracket of the printed second limit has `σ(s)` where `σ(t)` is meant (compare
(C.8)). (C.21) as a consequence of feasibility needs `ξ > x₀e^{∫₀ᵀ r}`: at equality `X ≡ x*` and
feasibility carries no information on `H̄`. The equivalence holds for each `x < x*(t)`. -/
theorem limits_and_C_21 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    {ψ : ℝ → ℝ} (hA3 : M.Assumption3 ψ) (ξ : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {vh : ℝ → Fin m → ℝ} (hvh : M.RightContSqInt vh) :
    (∀ t ∈ Ico 0 M.T, ∀ x, x < M.xStar ξ t → ∀ π : Fin m → ℝ,
      ∃ (Xh : ℝ → Ω → ℝ) (Xε : ℝ → ℝ → Ω → ℝ),
        M.IsUniqueWealthFrom P F W (fun s y => (M.xStar ξ s - y) • vh s) t x Xh ∧
        MemLp (Xh M.T) 2 P ∧
        (∀ ε ∈ Ioo 0 (M.T - t),
          M.IsUniqueWealthFrom P F W
            (spike t ε (fun _ _ => π) (fun s y => (M.xStar ξ s - y) • vh s)) t x (Xε ε) ∧
            MemLp (Xε ε M.T) 2 P) ∧
        Tendsto (fun ε => ((∫ ω, Xε ε M.T ω ∂P) - ∫ ω, Xh M.T ω ∂P) / ε) (𝓝[>] 0)
          (𝓝 ((M.xStar ξ t - x) * Real.exp (∫ s in t..M.T, (M.r s - M.b s ⬝ᵥ vh s)) *
            (M.b t ⬝ᵥ ((1 / (M.xStar ξ t - x)) • π) - M.b t ⬝ᵥ vh t))) ∧
        Tendsto (fun ε => (variance (Xε ε M.T) P - variance (Xh M.T) P) / ε) (𝓝[>] 0)
          (𝓝 (2 * (M.xStar ξ t - x) ^ 2 *
            Real.exp (2 * ∫ s in t..M.T, (M.r s - M.b s ⬝ᵥ vh s)) *
            Real.exp (∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ vh s)) *
            ((1 / 2) * (sqNorm ((M.σ t)ᵀ *ᵥ ((1 / (M.xStar ξ t - x)) • π)) -
                sqNorm ((M.σ t)ᵀ *ᵥ vh t)) -
              (1 - Real.exp (-∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ vh s))) *
                (M.b t ⬝ᵥ ((1 / (M.xStar ξ t - x)) • π) - M.b t ⬝ᵥ vh t)))) ∧
        (M.targetAspiration ψ ξ t x ≤ ∫ ω, Xh M.T ω ∂P ↔ 0 ≤ M.Hbar ψ vh t)) ∧
    (M.x₀ * Real.exp (∫ s in (0 : ℝ)..M.T, M.r s) < ξ →
      M.Feasible P F W (M.targetAspiration ψ ξ) (fun s y => (M.xStar ξ s - y) • vh s) →
      ∀ t ∈ Ico 0 M.T, 0 ≤ M.Hbar ψ vh t) := by sorry

end DynTargetMV
