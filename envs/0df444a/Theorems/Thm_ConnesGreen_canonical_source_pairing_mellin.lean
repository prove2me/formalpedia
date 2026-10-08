-- Prove2me | Theorems.Thm_ConnesGreen_canonical_source_pairing_mellin
-- name    : ConnesGreen.canonical_source_pairing_mellin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:49:50.328671+00:00
-- url     : https://prove2.me/theorems/376ddd62-cec8-4ecb-8652-49ec614c706c
-- title:
--   The original physical-source Green pairing equals its Mellin coefficient
-- statement:
--   For every positive window T, original supported smooth compact test g and actual zeta zero rho, the inner product of the original physical source at rho with the embedded original source Lg equals the Mellin transform of g at rho. The reflection in the original source frequency accounts exactly for conjugate linearity. Original completion, load Lg and analytic zero carrier are retained.
-- source:
--   monocap-tech/weil at 28829dbeeee2ba23d6c0f3cedaf22952174099c2; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_source_pairing_mellin (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) (ρ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ = mellinHat g ρ.1 := by sorry
