-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_uniform_restored_arithmetic_margin
-- name    : ConnesGreen.canonical_quartet_uniform_restored_arithmetic_margin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T03:24:54.775675+00:00
-- url     : https://prove2.me/theorems/f16784b9-26d3-460d-9f4e-bbbb5c1ebdfb
-- title:
--   One actual-zero quartet test gives a common full-background arithmetic violation on every larger window
-- statement:
--   For every actual nontrivial zeta zero ρ off the critical line, there exist a positive support radius t, one original supported smooth test g with the prescribed Mellin values on its quartet, and fixed numbers 0<η<1/2 and m>0, such that Re W(g*starInv(g))<−1/2 and for EVERY positive window T≥t the SAME test is supported there and
--   $$
--   m\le \|M_{T,Q}^*x_g\|^2-((1/2-\eta)^{-1}-1)\left(\operatorname{Re}W(g*\operatorname{starInv}(g))+\|M_{T,Q}^*x_g\|^2+\|B_{T,Q}^*x_g\|^2\right).
--   $$
--   Here Q is the original quartet of ρ, x_g is the original physical-carrier embedding of Lg at T, M is the selected synthesis and B is the COMPLETE actual-negative complement outside Q, with the original analytic multiplicities and reflection normalization. The test, loss η and positive violation margin m are chosen before T and work uniformly in every larger original carrier; no operators on different carriers are identified. No finite-off-axis assumption, arithmetic positivity premise, regularization or finite restoration cutoff occurs. The amplified support t is not asserted to belong to the intended critical window. This quantitative obstruction does not locate that critical window, prove its desired arithmetic lower bound or unconditional neutral-shell control, or prove RH. The existing full-Weil negative witness is reused, not claimed as newly discovered. RPB108 original-form attachments remain separate future formalization work.
-- source:
--   New closed consequence of the accepted canonical_quartet_selected_mellin_witness, canonical_actor_test_norms_window_independent and canonical_signed_actor_arithmetic, on the unchanged native Connes–Weil original carrier. Full native proof: UniformRestoredArithmeticMargin.lean in the accompanying checkpoint. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ConnesRZQuartet
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_quartet_uniform_restored_arithmetic_margin
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ t : ℝ, ∃ ht : 0 < t, ∃ g : ℝ → ℂ, SupportedTest t g ∧
      (∀ τ ∈ quartet ρ, mellinHat g τ.1 = packetValues ρ.1 τ.1) ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) ∧
      ∃ η m : ℝ, 0 < η ∧ η < 1 / 2 ∧ 0 < m ∧
        ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T → SupportedTest T g ∧
          m ≤ ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 -
            ((1 / 2 - η)⁻¹ - 1) *
              ((weilDistribution (conv g (starInv g))).re +
                ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2) := by sorry
