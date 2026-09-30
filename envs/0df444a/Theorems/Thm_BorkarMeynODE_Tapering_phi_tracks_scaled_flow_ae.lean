-- Prove2me | Theorems.Thm_BorkarMeynODE_Tapering_phi_tracks_scaled_flow_ae
-- name    : BorkarMeynODE.Tapering.phi_tracks_scaled_flow_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:45:03.075983+00:00
-- url     : https://prove2.me/theorems/11bd7557-8a8f-4b1e-8047-7f6f75513022
-- title:
--   Lemma 4.6 — a.s. the scaled interpolation tracks $\hat\phi$ and stays bounded
-- statement:
--   Assume (A1) for $(h,h_\infty)$, (A2) with constant $C_0$ for the natural filtration of $X$, and (TS); fix $T>0$. Let $X$ follow the recursion (1.1) with $\mathsf E[\|X(0)\|^2]<\infty$, let $\phi$ be the scaled interpolated process, and let $\hat\phi$ be, on every sample path, the piecewise solution of the scaled ODE (4.1) restarted at $\phi(T(j))$ at each block start. Then with probability one:
--
--   1. $\|\phi(t)-\hat\phi(t)\|\to0$ as $t\to\infty$;
--   2. $\displaystyle\sup_{t\ge0}\|\phi(t)\|<\infty$.
--
--   This is the approximation step of the O.D.E. method: after rescaling, the stochastic iterates follow the deterministic ODE flow asymptotically. Combined with Lemma 4.4 it yields the almost sure boundedness of Theorem 2.1 (i).
--
--   **Formalization Note** $\hat\phi$ is any family of functions satisfying the defining predicate on every sample path; by existence and uniqueness of forward solutions this is the paper's $\hat\phi$. "$\sup_{t\ge0}\|\phi(t)\|<\infty$" is written as boundedness above of $\{\|\phi(t)\|:t\ge0\}$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 463, Lemma 4.6

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_ODEStability
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
import Definitions.Def_BorkarMeynODE_Tapering_SAModel
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
import Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation
import Definitions.Def_BorkarMeynODE_Tapering_FlowsOnBlocks

namespace BorkarMeynODE.Tapering

open MeasureTheory Filter Topology

/-- **Lemma 4.6** (Borkar–Meyn 2000, p. 463). Assume (A1), (A2) with constant `C₀` for the
natural filtration of `X`, (TS), a block length `T > 0`, and `E‖X(0)‖² < ∞`. Let `φ̂` be, on
every sample path, the piecewise solution of (4.1) restarted at `φ(T(j))` on each block. Then
with probability one
(i) `‖φ(t) − φ̂(t)‖ → 0` as `t → ∞`, and
(ii) `sup_{t≥0} ‖φ(t)‖ < ∞`. -/
theorem phi_tracks_scaled_flow_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ) (C₀ : ℝ)
    (hA1 : AssumptionA1 h hInf) (hTS : TaperingStepsize a) (T : ℝ) (hT : 0 < T)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (hrec : IsSARecursion h a X M) (hA2 : AssumptionA2 P X M hX C₀)
    (hX0 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) P)
    (φh : Ω → ℝ → EuclideanSpace ℝ (Fin d))
    (hφh : ∀ ω, IsScaledFlowOnBlocks h a T (fun n => X n ω) (φh ω)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun t => ‖phi a T (fun n => X n ω) t - φh ω t‖) atTop (𝓝 0) ∧
      BddAbove ((fun t => ‖phi a T (fun n => X n ω) t‖) '' Set.Ici 0) := by sorry

end BorkarMeynODE.Tapering
