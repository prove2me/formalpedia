-- Prove2me | Theorems.Thm_DynTargetMV_theorem_1_iii
-- name    : DynTargetMV.theorem_1_iii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:48.089246+00:00
-- url     : https://prove2.me/theorems/176a2566-40b3-4018-90ef-fb039d10d727
-- title:
--   Theorem 1 (iii) — $\hat\pi(t,x)=v^*(t)(x^*(t)-x)$ for the aspiration target (corrected: $\Pi$ is the time-$t$ self's set; $\xi>x_0e^{\int r}$ in uniqueness)
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let Assumptions 2, 3 and 4 hold, with $v^*$ the solution of (2.10). Let $L$ be the target (2.9) with aspiration level $\xi\ge x_0e^{\int_0^Tr(s)ds}$, and let $x^*(t)=\xi e^{-\int_t^Tr(s)ds}$. If
--   $$
--   e^{-\int_t^T\|\sigma(s)^\top v^*(s)\|^2ds}\ge1-\frac{\psi(t)}{\rho(t)},\quad t\in[0,T), \tag{2.13}
--   $$
--   then
--   $$
--   \hat\pi(t,x)=v^*(t)(x^*(t)-x),\quad t\in[0,T),\ x\in\mathbb R, \tag{2.14}
--   $$
--   is an equilibrium strategy. If $\xi>x_0e^{\int_0^Tr(s)ds}$, any equilibrium strategy $\hat\pi$ such that $\hat\pi(t,x)/(x^*(t)-x)$ is independent of $x\in\mathbb R$ and right-continuous, square-integrable in $t\in[0,T)$ is given by (2.14), provided there exists $\delta_0>0$ with
--   $$
--   e^{-\int_t^T\|\sigma(s)^\top v^*(s)\|^2ds}\ge1-\frac{\psi(t)}{\rho(t)}+\delta_0,\quad t\in[0,T). \tag{2.15}
--   $$
--   Part (iii) of the main result: the agent invests in proportion to the distance from the aspiration path.
--
--   Differences from the source:
--   - correction: Π^π̂_{t,x} (p.8) asks that π_{t,ε,π} be feasible in the sense of p.7, with all constraints at all times along the path from x₀ → Π requires Qπ ≥ 0 and, for all small ε, a unique solution from (t,x) with square-integrable strategy and terminal value and E[X(T)] ≥ L(t,x); reason: the printed set makes the uniqueness clauses false: with m = d = 1, r = 0, b = σ = 1, Q = 0, T = 1, x₀ = γ = 1, ψ ≡ 1, the strategy π̃ ≡ e − 1 is an equilibrium of (ii) under the printed Π, and it is not (2.12); and the printed Π can be empty for target (2.7). The corrected set is what (C.10), (C.11), p.26, test
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
--   - encoding: a standard d-dimensional Brownian motion, with the filtration left implicit → IsStdBM: a filtered probability space with the usual conditions, Brownian on [0,T], coordinates given by the published BrownianOn, coordinate increments independent, vector increment independent of F r; reason: strong solutions live on the augmented Brownian filtration, which satisfies the usual conditions, and only [0,T] is used
--   - encoding: the Itô integral ∫π⊤σ dW → the sum over j of published HasItoIntegral integrals against W j, with the integrand set to 0 at the single time T, plus a.s. finite energy of π; reason: a strategy is a function on [0,T), the time T is null, and the energy clause follows from Assumption 1 (ii) for any Itô integrand
--   - encoding: E_t and var_t, conditional on the information at time t → at (t,x): mean and variance of the solution started at (t,x); along the agent's own path: condExp given F t; reason: p.7: the conditional law of X(T) depends on the wealth at time t only
--   - encoding: a feedback strategy is a measurable function on [0,T)×ℝ → a total function ℝ → ℝ → ℝ^m with measurability asked on [0,T)×ℝ only; reason: its values outside [0,T)×ℝ are never used
--   - encoding: Definition 1 takes for granted that var_t(X^π̂(T)) is defined for reachable (t,x) → IsEquilibrium also requires a unique solution of π̂ from each reachable (t,x), with L² terminal value; reason: so that (2.5) is not vacuous; this is automatic for the strategies of Theorem 1, which are affine in wealth with square-integrable coefficients
--   - encoding: 𝕏_t uses the distribution of X^π̂(t) conditional on the information at time 0 → the law of X^π̂(t) under P; reason: the start x₀ is deterministic, and the solution from it does not depend on the time-0 information
--   - encoding: Qπ(s,X(s)) ≥ 0, s ∈ [t,T), in feasibility → a.s., for all s ∈ [0,T) simultaneously; reason: the pathwise reading of the printed constraint
--   - correction: the uniqueness clause of Theorem 1 (iii) allows ξ = x₀e^{∫₀ᵀ r} → uniqueness assumes ξ > x₀e^{∫₀ᵀ r}; existence keeps ξ ≥ x₀e^{∫₀ᵀ r}; reason: at equality the clause is false: m = d = 1, r = 0, b = σ = 1, Q = 0, T = 1, x₀ = ξ = 1, ψ ≡ 2 satisfy (2.15) with δ₀ = 1, X ≡ 1 under π̂ ≡ 0, the variance is 0, so π̂ ≡ 0 is an equilibrium of the class, and it is not (2.14)
--   - reading: "π̂(t,x)/(x*(t) − x) is independent of x", undefined at x = x*(t) → π̂(t,x) = (x*(t) − x)v̂(t) on [0,T)×ℝ, with v̂ right-continuous and square-integrable; reason: this is the proof's reading, p.29
--   - encoding: v*(t), the unique solution of (2.10), t ∈ [0,T) → a function v with IsQPSol at every t ∈ [0,T); reason: the solution is unique, so v = v* on [0,T), and v is not used elsewhere
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1 (iii), pp.10–11

import Definitions.Def_DynTargetMV_halfQuad
import Definitions.Def_DynTargetMV_IsOptimal
import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_Assumption2
import Definitions.Def_DynTargetMV_Market_Assumption3
import Definitions.Def_DynTargetMV_Market_Assumption4
import Definitions.Def_DynTargetMV_Market_IsQPSol
import Definitions.Def_DynTargetMV_Market_RightContSqInt
import Definitions.Def_DynTargetMV_Market_IsEquilibrium
import Definitions.Def_DynTargetMV_IsStdBM
import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_Market_rho
import Definitions.Def_DynTargetMV_Market_targetAspiration
import Definitions.Def_DynTargetMV_Market_xStar

open MeasureTheory Set Matrix

namespace DynTargetMV

/-- **Theorem 1 (iii)**, corrected. For target (2.9) with `ξ ≥ x₀e^{∫₀ᵀ r}`: under (2.13),
`π̂(t,x) = v*(t)(x*(t) − x)`, (2.14), is an equilibrium strategy; and, when `ξ > x₀e^{∫₀ᵀ r}`, under (2.15) any
equilibrium strategy such that `π̂(t,x)/(x*(t) − x)` is independent of `x` and right-continuous,
square-integrable in `t ∈ [0,T)` is given by (2.14). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Theorem 1 (iii), pp.10–11.

**Formalization Note** The printed uniqueness clause allows `ξ = x₀e^{∫₀ᵀ r}`, where it is false: `m = d = 1`,
`r = 0`, `b = σ = 1`, `Q = 0`, `T = 1`, `x₀ = ξ = 1`, `ψ ≡ 2` satisfy (2.15) with `δ₀ = 1`, and `π̂ ≡ 0` is an
equilibrium of the class, not (2.14). Equilibrium is Definition 1 with the corrected `Π`. -/
theorem theorem_1_iii {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) {ψ : ℝ → ℝ} (hA3 : M.Assumption3 ψ) {v : ℝ → Fin m → ℝ}
    (hv : ∀ t ∈ Ico 0 M.T, M.IsQPSol ψ t (v t)) (hA4 : M.Assumption4 v)
    {ξ : ℝ} (hξ : M.x₀ * Real.exp (∫ s in (0 : ℝ)..M.T, M.r s) ≤ ξ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T) :
    ((∀ t ∈ Ico 0 M.T,
          1 - ψ t / M.rho t ≤ Real.exp (-∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ v s))) →
        M.IsEquilibrium P F W (M.targetAspiration ψ ξ) (fun t x => (M.xStar ξ t - x) • v t)) ∧
      (M.x₀ * Real.exp (∫ s in (0 : ℝ)..M.T, M.r s) < ξ →
        (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ t ∈ Ico 0 M.T,
          1 - ψ t / M.rho t + δ₀ ≤ Real.exp (-∫ s in t..M.T, sqNorm ((M.σ s)ᵀ *ᵥ v s))) →
        ∀ (πh : ℝ → ℝ → Fin m → ℝ) (vh : ℝ → Fin m → ℝ),
          M.IsEquilibrium P F W (M.targetAspiration ψ ξ) πh → M.RightContSqInt vh →
          (∀ t ∈ Ico 0 M.T, ∀ x, πh t x = (M.xStar ξ t - x) • vh t) →
          ∀ t ∈ Ico 0 M.T, ∀ x, πh t x = (M.xStar ξ t - x) • v t) := by sorry

end DynTargetMV
