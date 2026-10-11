-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_actual_zero_tail_control
-- name    : ConnesGreen.canonical_uniform_actual_zero_tail_control
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T17:23:50.859585+00:00
-- url     : https://prove2.me/theorems/708f446d-c43a-4810-9f70-d04b9388e32d
-- title:
--   Uniform fixed-window actual-zero and full-background finite-tail control
-- statement:
--   For EVERY positive original window t, EVERY finite set S of ACTUAL critical-strip zeta zeros, and EVERY ε>0, there is a finite ACTUAL-zero set F containing S, chosen BEFORE and uniformly for EVERY original SupportedTest t g with original physical source norm squared ≤1. The full squared-norm sum of the original positive-plus-negative columns outside F is <ε, independently of g. The complete ACTUAL convolved zero contribution outside F, with actual zeta multiplicities, has a summable norm series with its tsum <ε. The complete original unselected-negative background energy outside F is nonnegative and <ε. ORIGINAL S-custody is retained by the exact identity: background outside S equals the finite negative pairing energy indexed by F\S plus the complete background outside F. The complete positive adjoint energy minus its finite pairing-energy sum over F is nonnegative and <ε. No reflection-closure, off-critical-line assumption, Weil positivity, RH, endpoint hypothesis or arithmetic lower-bound assumption is used. Norm ≤1 includes the zero test. F is an existential finite actual-zero set, not a claimed effective height cutoff. This is uniform finite-tail control at one FIXED original support window and norm bound, not decay of the entire background outside S, a uniform estimate over unbounded windows, or control stable under a singular ordered selected inverse.
-- source:
--   For EVERY positive original window t, EVERY finite set S of ACTUAL critical-strip zeta zeros, and EVERY ε>0, there is a finite ACTUAL-zero set F containing S, chosen BEFORE and uniformly for EVERY original SupportedTest t g with original physical source norm squared ≤1. The full squared-norm sum of the original positive-plus-negative columns outside F is <ε, independently of g. The complete ACTUAL convolved zero contribution outside F, with actual zeta multiplicities, has a summable norm series with its tsum <ε. The complete original unselected-negative background energy outside F is nonnegative and <ε. ORIGINAL S-custody is retained by the exact identity: background outside S equals the finite negative pairing energy indexed by F\S plus the complete background outside F. The complete positive adjoint energy minus its finite pairing-energy sum over F is nonnegative and <ε. No reflection-closure, off-critical-line assumption, Weil positivity, RH, endpoint hypothesis or arithmetic lower-bound assumption is used. Norm ≤1 includes the zero test. F is an existential finite actual-zero set, not a claimed effective height cutoff. This is uniform finite-tail control at one FIXED original support window and norm bound, not decay of the entire background outside S, a uniform estimate over unbounded windows, or control stable under a singular ordered selected inverse.
--
--   Standalone proofs, unchanged clean native checkout head ada7948cb459fd21d400cd8f2a92e87672e31f2d, no new repository commit or CI head. Original RPB108 original-form attachments remain a separate future formalization task.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_uniform_actual_zero_tail_control
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (ε : ℝ) (hε : 0 < ε) :
    let v := fun τ : CriticalZeros => sourceEmbed t (actualGreenSource τ)
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∑' τ : CriticalZeros, if τ ∈ F then 0 else
        ‖positiveGreenColumn v τ‖ ^ 2 + ‖negativeGreenColumn v τ‖ ^ 2) < ε ∧
      ∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
        let x := sourceEmbed t (problemOneL g)
        Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
          (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
        (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
          (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε ∧
        (0 ≤ ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 ∧
          ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 < ε) ∧
        ‖(canonicalBackgroundSynthesis t ht S).adjoint x‖ ^ 2 =
          (∑ τ ∈ F \ S, ‖⟪negativeGreenColumn v τ, x⟫_ℂ‖ ^ 2) +
            ‖(canonicalBackgroundSynthesis t ht F).adjoint x‖ ^ 2 ∧
        (0 ≤ ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
          (∑ τ ∈ F, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) ∧
          ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
            (∑ τ ∈ F, ‖⟪positiveGreenColumn v τ, x⟫_ℂ‖ ^ 2) < ε) := by sorry
