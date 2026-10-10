-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_bounded_selected_tests_iff_physical_margin
-- name    : ConnesGreen.canonical_uniform_bounded_selected_tests_iff_physical_margin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T07:42:44.467981+00:00
-- url     : https://prove2.me/theorems/40f0e212-3e78-47bc-81ab-83dabb578fa8
-- title:
--   Bounded normalized tests and a uniform full-background physical margin
-- statement:
--   Fix any positive c and any finite selection S of ACTUAL critical-strip zeta zeros, with the original reflected-pair negative synthesis. On EVERY positive window c<T<c+1, the following two family statements are equivalent. (1) There are constants δ in (0,1) and M>0, chosen before T, such that each T admits an ORIGINAL supported admissible test with selected adjoint energy exactly one, global Dirichlet energy at most M, and Re W(g*starInv g) plus COMPLETE actual unselected-negative adjoint energy strictly below −δ. (2) There is one ε>0, chosen before T, such that each T admits an ORIGINAL supported admissible test with physical source norm squared exactly one and the same restored Weil value strictly below −ε. The test varies with T. This proves an equivalence, not existence of either family. No endpoint/cut location, uniform witness boundedness, compactness, critical-line classification, spectral gap, finite-off-axis premise, or RH is inferred.
-- source:
--   New closed quantitative reduction on original supported tests and actual-zero syntheses. A uniform negative complete-background margin at unit selected energy, together with a uniform bound on global Dirichlet energy, is equivalent to a uniform negative complete-background margin at unit physical-source energy on c<T<c+1. All four dependencies are accepted. Fixed outer-window actor custody supplies the uniform selected operator bound; original source identity and full arithmetic energy give exact scalar homogeneity. Neither family, endpoint failure, compactness nor RH is assumed or established. Original RPB108 form attachments remain future formalization.

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

theorem ConnesGreen.canonical_uniform_bounded_selected_tests_iff_physical_margin
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros) :
    (∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ M : ℝ, 0 < M ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
          ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
            (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) ≤ M ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ) ↔
    (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) := by sorry
