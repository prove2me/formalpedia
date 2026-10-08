-- Prove2me | Theorems.Thm_ConnesGreen_exists_original_neutral_persistence_small_support
-- name    : ConnesGreen.exists_original_neutral_persistence_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:35:18.22627+00:00
-- url     : https://prove2.me/theorems/b2c072e1-5346-49b7-9298-bef57f2dbd92
-- title:
--   Original window inclusion exists with neutral-kernel persistence inside the certified interval
-- statement:
--   For 0<t<=T<=positiveSupportRadius and every unchanged finite packet S of actual zeta zeros, an original complex linear isometric window inclusion exists, agrees with the original source embeddings of every test supported in t, and transports the original selected signed covariance kernel in both directions. The original inclusion and its source custody are constructed from accepted original developments; no inclusion, kernel persistence or positivity assumption is added. This bounded-interval result does not establish neutral-shell control at an unidentified critical endpoint.
-- source:
--   monocap-tech/weil at 7c8f9fd8159da27ab0aae95d6b1e63080a1834d2; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.exists_original_neutral_persistence_small_support (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (hTr : T ≤ positiveSupportRadius)
    (S : Finset CriticalZeros) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      ∀ x : Physical t,
        (canonicalPositiveCovariance t ht -
          canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
        (canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by sorry
