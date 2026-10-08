-- Prove2me | Theorems.Thm_ConnesGreen_canonical_supported_neutral_zero_small_support
-- name    : ConnesGreen.canonical_supported_neutral_zero_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:35:53.394229+00:00
-- url     : https://prove2.me/theorems/a992a638-0ae5-40aa-9aaa-05c5ac908a82
-- title:
--   Original supported tests with a neutral selected quadratic value vanish inside the certified interval
-- statement:
--   For 0<T<=positiveSupportRadius, every unchanged finite actual-zero packet S and every original supported test g, zero original selected quadratic value of sourceEmbed T (problemOneL g) implies g=0. The public premise unfolds exactly native selectedQuadratic as the difference of original adjoint norm squares. The proof uses accepted original Weil half-mass positivity, accepted full signed actor arithmetic, and the convergent exact selected/background partition of the original negative analysis. It proves zero for supported tests, not for every completed-carrier kernel vector. No density extension, arithmetic endpoint budget or RH is claimed.
-- source:
--   monocap-tech/weil at 7c8f9fd8159da27ab0aae95d6b1e63080a1834d2; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_supported_neutral_zero_small_support (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest T g)
    (hn : ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 0) : g = 0 := by sorry
