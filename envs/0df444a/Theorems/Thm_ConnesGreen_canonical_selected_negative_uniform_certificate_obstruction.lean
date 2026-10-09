-- Prove2me | Theorems.Thm_ConnesGreen_canonical_selected_negative_uniform_certificate_obstruction
-- name    : ConnesGreen.canonical_selected_negative_uniform_certificate_obstruction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T23:58:23.509649+00:00
-- url     : https://prove2.me/theorems/4def6bc2-d629-447b-bfc3-4fc88f70ae5d
-- title:
--   One original negative witness defeats every finite selected certificate at small accuracy
-- statement:
--   At one positive original window and unchanged finite selected actual-zero packet S, an original physical vector whose selected quadratic form is strictly negative yields one positive threshold δ₀. For every positive δ at most δ₀ and EVERY finite actual-zero cutoff F, the original selected correction fails nonnegativity. F need not contain S or be reflection-closed. Consequently requiring containment, reflection closure and the complete positive tail bound cannot repair nonnegativity. The selected actor, physical carrier, analytic multiplicities and reflected-pair normalization are unchanged. No RH or unconditional arithmetic estimate is proved.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteCertificateObstruction.lean, exact declaration ConnesGreen.canonical_selected_negative_uniform_certificate_obstruction, compiling local source commit fca7dd5f25d79b1d073e5e0b5d0f0b08ed2f3141. Existing original Green/actor definitions and certified quartet-window/selected-test/arithmetic criteria are reused unchanged.

import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.canonical_selected_negative_uniform_certificate_obstruction
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (x : Physical t)
    (hneg : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 < 0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ F : Finset CriticalZeros,
        ¬ 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ := by sorry
