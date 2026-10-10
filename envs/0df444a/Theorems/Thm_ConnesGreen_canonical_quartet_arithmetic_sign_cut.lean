-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_arithmetic_sign_cut
-- name    : ConnesGreen.canonical_quartet_arithmetic_sign_cut
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T04:42:40.219693+00:00
-- url     : https://prove2.me/theorems/4a128e64-1a0e-4a67-8b8d-58d96f769139
-- title:
--   Exact actual-quartet arithmetic sign cut with complete-tail negative tests above the boundary
-- statement:
--   For every actual nontrivial zeta zero ρ off the critical line there exists a finite real cut c at least the already certified positive support radius. For each positive original window T, EVERY original smooth test g supported strictly in that window satisfies Re W(g*starInv(g))+||B_Q* x_g||²≥0 if and only if T≤c. Here Q is the original quartet of ρ, x_g is the original physical-carrier embedding of Lg, and B_Q is the COMPLETE actual-negative complement outside that quartet, with analytic multiplicities and reflected normalization unchanged. The boundary T=c is included in the nonnegative side.
--
--   For EVERY positive T>c there exists an original supported test g with ||B_Q* x_g||²<−Re W(g*starInv(g)), and consequently Re W(g*starInv(g))<0. The cut is chosen before T; the test may depend on T. This includes arbitrarily close windows to the right of c. It asserts no common test, uniform negative margin, prescribed Mellin interpolation values, or identification of c with an intended critical endpoint. No finite-off-axis hypothesis or arithmetic positivity premise is introduced. The exact complete-tail balance is proved, not assumed. Inner half-bound at c does not assert the ordered support-right half-bound there; its arithmetic/jump-budget obligation and physical neutral-shell control remain open. RH is not established. RPB108 original-form attachments remain a separate future formalization task.
-- source:
--   New closed consequence of the accepted canonical_quartet_last_inner_half_window, canonical_negative_tests_after_half_cut and canonicalPicardMarker_lower_iff_restored_weil_actor_bound, on the unchanged native Connes–Weil original carrier. Full native proof: QuartetArithmeticSignCut.lean in the accompanying checkpoint. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ConnesRZQuartet
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_quartet_arithmetic_sign_cut
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        (∀ g : ℝ → ℂ, SupportedTest T g →
          0 ≤ (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2) ↔ T ≤ c) ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 <
              -(weilDistribution (conv g (starInv g))).re ∧
          (weilDistribution (conv g (starInv g))).re < 0 := by sorry
