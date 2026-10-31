-- Prove2me | Theorems.Thm_DynTargetMV_claim_C_22
-- name    : DynTargetMV.claim_C_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:47.273422+00:00
-- url     : https://prove2.me/theorems/88568740-abd9-4ed8-b974-3227afbf9105
-- title:
--   (C.22), p.30 — equilibrium iff $\hat v(t)$ solves (C.22) (corrected: $\Pi$ is the time-$t$ self's set; $\xi>x_0e^{\int r}$)
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let Assumptions 2, 3 and 4 hold, with $v^*$ the solution of (2.10). Let $L$ be the target (2.9) with $\xi>x_0e^{\int_0^Tr(s)ds}$, and let $\hat\pi(t,x)=\hat v(t)(x^*(t)-x)$ be a feasible strategy with $\hat v$ right-continuous and square-integrable on $[0,T)$. Then $\hat\pi$ is an equilibrium strategy if and only if, for each $t\in[0,T)$, $\hat v(t)$ is the optimal solution of
--   $$
--   \min_{v\in\mathbb R^m}\ \tfrac12v^\top\sigma(t)\sigma(t)^\top v+\varphi(t;\hat\pi)b(t)^\top v\quad\text{subject to}\quad\bigl(b(t)^\top v-b(t)^\top\hat v(t)\bigr)\mathbf 1_{\bar H(t;\hat\pi)=0}\ge0,\ Qv\ge0,
--   $$
--   where $\varphi(t;\hat\pi):=-\bigl(1-e^{-\int_t^T\|\sigma(s)^\top\hat v(s)\|^2ds}\bigr)\in(-1,0]$.
--
--   The negative linear coefficient is what makes condition (2.13) necessary for this target.
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
--   - correction: the argument at p.29–30 allows ξ = x₀e^{∫₀ᵀ r} → ξ > x₀e^{∫₀ᵀ r} is assumed; reason: the proof needs a reachable x < x*(t); at equality X ≡ x*, and π̂ ≡ 0 is an equilibrium whatever H̄ and (C.22) say (m = d = 1, r = 0, b = σ = 1, Q = 0, T = 1, x₀ = ξ = 1, ψ ≡ 2)
--   - encoding: the indicator 1_{…} in the first constraint → an implication from the indicated equality; reason: the same feasible set
--   - reading: the indicator of (C.22) is printed 1_{H(t;π̂)=0}, with H the quantity (C.17) of the premium target → the indicator of H̄(t;v̂) = 0, H̄ of (C.21); reason: in case (iii) the target condition is (C.21), and the same argument as case (i) puts the indicator on the target's slack, which here is H̄; H of (C.17) is not defined for target (2.9)
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.22), (C.23), p.30

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
import Definitions.Def_DynTargetMV_Market_phiGap
import Definitions.Def_DynTargetMV_Market_targetAspiration
import Definitions.Def_DynTargetMV_Market_xStar
import Definitions.Def_DynTargetMV_Market_Hbar

open MeasureTheory Set Matrix

namespace DynTargetMV

/-- The claim (C.22) for target (2.9), with `ξ > x₀e^{∫₀ᵀ r}`: a feasible `π̂(t,x) = v̂(t)(x*(t) − x)`, with `v̂`
right-continuous and square-integrable, is an equilibrium strategy if and only if for each `t ∈ [0,T)`,
`v̂(t)` is the optimal solution of (C.22), where `φ(t;π̂)` is (C.23). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.22), (C.23), p.30.

**Formalization Note** The indicator of (C.22) is an implication from `H̄(t;v̂) = 0`. `φ(t;π̂)` of (C.23)
is `−M.phiGap v̂ t`. The strict `ξ > x₀e^{∫₀ᵀ r}` is needed: at equality `X ≡ x*` and `π̂ ≡ 0` is an
equilibrium. `v` and Assumption 4 are the paper's standing assumptions. -/
theorem claim_C_22 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) {ψ : ℝ → ℝ} (hA3 : M.Assumption3 ψ) {v : ℝ → Fin m → ℝ}
    (hv : ∀ t ∈ Ico 0 M.T, M.IsQPSol ψ t (v t)) (hA4 : M.Assumption4 v)
    {ξ : ℝ} (hξ : M.x₀ * Real.exp (∫ s in (0 : ℝ)..M.T, M.r s) < ξ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {vh : ℝ → Fin m → ℝ} (hvh : M.RightContSqInt vh)
    (hfeas : M.Feasible P F W (M.targetAspiration ψ ξ) (fun t x => (M.xStar ξ t - x) • vh t)) :
    M.IsEquilibrium P F W (M.targetAspiration ψ ξ) (fun t x => (M.xStar ξ t - x) • vh t) ↔
      ∀ t ∈ Ico 0 M.T, IsOptimal
        (fun w => halfQuad (M.σ t * (M.σ t)ᵀ) w + (-M.phiGap vh t) * (M.b t ⬝ᵥ w))
        {w | (M.Hbar ψ vh t = 0 → M.b t ⬝ᵥ vh t ≤ M.b t ⬝ᵥ w) ∧ 0 ≤ M.Q *ᵥ w}
        (vh t) := by sorry

end DynTargetMV
