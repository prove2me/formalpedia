-- Prove2me | Theorems.Thm_ConnesGreen_canonical_neutral_kernel_persists_small_support
-- name    : ConnesGreen.canonical_neutral_kernel_persists_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:35:23.502364+00:00
-- url     : https://prove2.me/theorems/c163daa5-b38f-42f0-96c8-482dea975db4
-- title:
--   Original neutral kernels persist under every original window inclusion inside the certified interval
-- statement:
--   For 0<t<=T<=positiveSupportRadius, any unchanged finite packet S of actual zeta zeros, and every original complex linear isometric window inclusion U that agrees with source embeddings of all original supported tests, the original selected signed covariance vanishes at a physical vector x on window t if and only if it vanishes at U x on window T. The positivity requirement is discharged by the accepted original small-support covariance theorem. This is kernel persistence on arbitrary completed-carrier vectors inside the explicit interval, not a proof that these kernels are zero or a statement at the intended critical endpoint.
-- source:
--   monocap-tech/weil at 7c8f9fd8159da27ab0aae95d6b1e63080a1834d2; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_neutral_kernel_persists_small_support (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (hTr : T ≤ positiveSupportRadius)
    (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) (x : Physical t) :
    (canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
    (canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by sorry
