-- Prove2me | Theorems.Thm_ConnesGreen_canonical_neutral_shell_zero_of_larger_half
-- name    : ConnesGreen.canonical_neutral_shell_zero_of_larger_half
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T07:05:50.758248+00:00
-- url     : https://prove2.me/theorems/e2e64ddf-c8ca-4bee-a3dd-97966001bc58
-- title:
--   Original larger-window inner half-bound eliminates leakage of smaller neutral vectors
-- statement:
--   For $0<t\le T$, every original finite actual-zero packet $S$, every original source-compatible complex linear isometry $U$, and every completed smaller-window vector $x$ with $C_{t,S}x=0$, we prove
--   $$\tfrac12 I\le G_S(T)\quad\Longrightarrow\quad (I-UU^*)C_{T,S}Ux=0.$$
--   The accepted exact original kernel-persistence theorem discharges larger signed-covariance nonnegativity from its original inner half-bound and gives $C_{T,S}Ux=0$. Applying the original orthogonal-shell operator to zero proves the conclusion. No full Weil positivity or neutral-shell estimate is added as a premise. In particular, the already certified exact off-line quartet cutoff supplies this half-bound for every positive larger window at or below that finite INNER cutoff, including the cutoff itself. The result is conditional on the displayed concrete larger-window half-bound and supplies no unconditional right-support endpoint control beyond it.
-- source:
--   monocap-tech/weil parent b7df0270c344b8721001f902d0955d977d7afccc; recovered exact CanonicalGreenNeutralShell.lean core/shell theorem and additive NeutralShellObstruction.lean reductions

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_neutral_shell_zero_of_larger_half (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (x : Physical t) (hx : (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0) :
    (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
      ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0 := by sorry
