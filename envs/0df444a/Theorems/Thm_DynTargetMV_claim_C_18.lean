-- Prove2me | Theorems.Thm_DynTargetMV_claim_C_18
-- name    : DynTargetMV.claim_C_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:49.235178+00:00
-- url     : https://prove2.me/theorems/53d350db-85d4-4310-a4c1-917869f5af5d
-- title:
--   (C.18), p.28 — equilibrium iff $\hat\pi(t)$ solves (C.18) (corrected: $\Pi$ is the time-$t$ self's set)
-- statement:
--   Let $r,b,\sigma,Q$ be a market satisfying Assumption 1, with end date $T$ and initial wealth $x_0>0$, and let $W$ be a standard $d$-dimensional Brownian motion on a filtered probability space. Let Assumptions 2, 3 and 4 hold, with $v^*$ the solution of (2.10). Let $L$ be the target (2.8) with $\gamma>0$, and let $\hat\pi(t,x)=\hat\pi(t)$ be a feasible wealth-independent strategy, right-continuous and square-integrable on $[0,T)$. Then $\hat\pi$ is an equilibrium strategy if and only if, for any $t\in[0,T)$, $\hat\pi(t)$ is the optimal solution of
--   $$
--   \min_{\pi\in\mathbb R^m}\ \tfrac12\pi^\top\sigma(t)\sigma(t)^\top\pi\quad\text{subject to}\quad\bigl(b(t)^\top\pi-b(t)^\top\hat\pi(t)\bigr)\mathbf 1_{H(t;\hat\pi)=0}\ge0,\ Q\pi\ge0 ,
--   $$
--   where $H$ is (C.17).
--
--   This is the analogue of (C.14) for target (2.8).
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
--   - encoding: the indicator 1_{…} in the first constraint → an implication from the indicated equality; reason: the same feasible set
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.17), (C.18), p.28

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
import Definitions.Def_DynTargetMV_Market_targetPremium
import Definitions.Def_DynTargetMV_Market_Hpremium

open MeasureTheory Set Matrix

namespace DynTargetMV

/-- The claim (C.18) for target (2.8): a feasible wealth-independent `π̂(t,x) = p(t)`, right-continuous and
square-integrable, is an equilibrium strategy if and only if for any `t ∈ [0,T)`, `p(t)` is the optimal
solution of (C.18). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (C.17), (C.18), p.28.

**Formalization Note** The indicator of (C.18) is an implication from `H(t;π̂) = 0`. `v` and Assumption 4
are the paper's standing assumptions. -/
theorem claim_C_18 {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) {ψ : ℝ → ℝ} (hA3 : M.Assumption3 ψ) {v : ℝ → Fin m → ℝ}
    (hv : ∀ t ∈ Ico 0 M.T, M.IsQPSol ψ t (v t)) (hA4 : M.Assumption4 v)
    {γ : ℝ} (hγ : 0 < γ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Filtration ℝ mΩ}
    {W : Fin d → ℝ → Ω → ℝ} (hW : IsStdBM P F W M.T)
    {p : ℝ → Fin m → ℝ} (hp : M.RightContSqInt p)
    (hfeas : M.Feasible P F W (M.targetPremium ψ γ) (fun t _ => p t)) :
    M.IsEquilibrium P F W (M.targetPremium ψ γ) (fun t _ => p t) ↔
      ∀ t ∈ Ico 0 M.T, IsOptimal (halfQuad (M.σ t * (M.σ t)ᵀ))
        {π | (M.Hpremium ψ γ p t = 0 → M.b t ⬝ᵥ p t ≤ M.b t ⬝ᵥ π) ∧ 0 ≤ M.Q *ᵥ π}
        (p t) := by sorry

end DynTargetMV
