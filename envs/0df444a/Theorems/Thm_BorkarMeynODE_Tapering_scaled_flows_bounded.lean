-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_scaled_flows_bounded
-- name    : BorkarMeynODE.Tapering.scaled_flows_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:42:23.156493+00:00
-- url     : https://prove2.me/theorems/180730f4-d370-4c0e-b5e8-a18e72c08e19
-- title:
--   Lemma 4.2 — the piecewise solutions $\hat\phi$ and $\phi^\infty$ are uniformly bounded
-- statement:
--   Assume (A1) for $(h,h_\infty)$, fix a block length $T>0$, and let the step sizes satisfy (TS) or (BS). Then there is a constant $\bar C<\infty$ such that, for every sample path $\{X(n)\}$ (in particular for every initial condition $X(0)\in\mathbb R^d$), the piecewise solutions $\hat\phi$ of the scaled ODE (4.1) and $\phi^\infty$ of the fluid limit (1.5), restarted at $\phi(T(j))$ at each block start $T(j)$, satisfy
--   $$
--   \|\hat\phi(t)\| \le \bar C \quad\text{and}\quad \|\phi^\infty(t)\| \le \bar C, \qquad t\ge0 .
--   $$
--   The constant depends only on $h$ and $T$, not on the path.
--
--   Boundedness of $\hat\phi$ and $\phi^\infty$ is what allows the Lipschitz and Gronwall estimates of Lemmas 4.4 and 4.6 to be applied uniformly over blocks.
--
--   **Formalization Note** The page prints "$\hat\phi(t)\le\bar C$ and $\phi^\infty(t)\le\bar C$"; vectors in $\mathbb R^d$ are not ordered and the proof bounds $\|\hat\phi(t)\|^2$, so the norm bound is stated. The statement is made for every sequence $\{X(n)\}$, not only for paths of the recursion, since neither (1.1) nor (A2) is used; (A2), listed on the page, is therefore omitted.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 461, Lemma 4.2

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
import Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation
import Definitions.Def_BorkarMeynODE_Tapering_FlowsOnBlocks

namespace BorkarMeynODE.Tapering

/-- **Lemma 4.2** (Borkar–Meyn 2000, p. 461). Under (A1), for a fixed block length `T > 0` and
step sizes satisfying (TS) or (BS), there is a constant `C̄ < ∞` such that for every sample path
`x = (X(n))_n` (hence for every initial condition) the piecewise ODE solutions `φ̂` (solving
(4.1) on each block) and `φ^∞` (solving (1.5) on each block), restarted at `φ(T(j))` at every
block start, satisfy `‖φ̂(t)‖ ≤ C̄` and `‖φ^∞(t)‖ ≤ C̄` for all `t ≥ 0`.
The page prints `φ̂(t) ≤ C̄` and `φ^∞(t) ≤ C̄`; vectors in `ℝ^d` are not ordered and the proof
bounds `‖φ̂(t)‖²`, so the norm bound is stated. The bound is stated for every sequence `x`
(the proof uses neither the recursion (1.1) nor (A2)). -/
theorem scaled_flows_bounded {d : ℕ}
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hA1 : AssumptionA1 h hInf) (T : ℝ) (hT : 0 < T) (a : ℕ → ℝ)
    (ha : TaperingStepsize a ∨ BoundedStepsize a) :
    ∃ Cbar : ℝ,
      (∀ (x : ℕ → EuclideanSpace ℝ (Fin d)) (φh : ℝ → EuclideanSpace ℝ (Fin d)),
        IsScaledFlowOnBlocks h a T x φh → ∀ t : ℝ, 0 ≤ t → ‖φh t‖ ≤ Cbar) ∧
      (∀ (x : ℕ → EuclideanSpace ℝ (Fin d)) (φi : ℝ → EuclideanSpace ℝ (Fin d)),
        IsFluidFlowOnBlocks hInf a T x φi → ∀ t : ℝ, 0 ≤ t → ‖φi t‖ ≤ Cbar) := by sorry

end BorkarMeynODE.Tapering
