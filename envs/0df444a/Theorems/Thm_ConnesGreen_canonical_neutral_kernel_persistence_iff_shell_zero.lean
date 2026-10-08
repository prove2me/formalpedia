-- Prove2me | Theorems.Thm_ConnesGreen_canonical_neutral_kernel_persistence_iff_shell_zero
-- name    : ConnesGreen.canonical_neutral_kernel_persistence_iff_shell_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T07:05:58.427267+00:00
-- url     : https://prove2.me/theorems/86ee4f27-ad4a-41ed-8a8e-26872a26cc4c
-- title:
--   Exact original neutral-persistence obstruction is shell leakage on the smaller kernel
-- statement:
--   For EVERY original source-compatible complex linear isometry between $0<t\le T$ and EVERY original finite actual-zero packet $S$, we prove
--   $$[\forall x,\ C_{t,S}x=0\Longleftrightarrow C_{T,S}Ux=0]
--   \Longleftrightarrow [\forall x,\ C_{t,S}x=0\Longrightarrow (I-UU^*)C_{T,S}Ux=0].$$
--   All vectors range over the ORIGINAL completed Physical(t) carrier, not merely supported test vectors. A closed local proof of the exact original core-and-shell equivalence uses accepted source-adjoint custody and signed-covariance compression. Persistence implies shell vanishing by its forward implication and that equivalence. Conversely the shell-zero property and core neutrality give larger neutrality; larger neutrality always gives core neutrality by exact compression. This identifies the entire remaining obstruction for this specified original inclusion as the displayed concrete operator shell on the smaller kernel. It does not supply that shell estimate unconditionally and does not replace a separately prescribed ordered endpoint with a finite larger window.
-- source:
--   monocap-tech/weil parent b7df0270c344b8721001f902d0955d977d7afccc; recovered exact CanonicalGreenNeutralShell.lean core/shell theorem and additive NeutralShellObstruction.lean reductions

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_neutral_kernel_persistence_iff_shell_zero (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) :
    (∀ x : Physical t, (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔ (canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0) ↔
    (∀ x : Physical t, (canonicalPositiveCovariance t ht - canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 → (1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint)
      ((canonicalPositiveCovariance T hT - canonicalSelectedSynthesis T hT S ∘L
        (canonicalSelectedSynthesis T hT S).adjoint) (U x)) = 0) := by sorry
