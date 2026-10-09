-- Prove2me | Theorems.Thm_ConnesGreen_canonical_selected_form_ge_overlap_shift
-- name    : ConnesGreen.canonical_selected_form_ge_overlap_shift
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:45:59.19711+00:00
-- url     : https://prove2.me/theorems/5682ec49-b0e6-4b4b-ba3e-15199c48a1fb
-- title:
--   Improved arithmetic shift controls every original selected physical vector
-- statement:
--   Let $0<T\le R$ and let $S$ be any finite packet of ACTUAL zeta-zero indices. On the ORIGINAL completed physical carrier at $T$, with the unchanged positive and selected negative synthesis maps $P_T,N_{T,S}$, the explicit arithmetic overlap shift satisfies $$\|P_T^*x\|^2-\|N_{T,S}^*x\|^2\ge-K_R\|x\|^2\qquad\text{for every }x.$$ The complete actual negative complement is handled by its exact energy partition. This is a shifted lower bound; it does not assert nonnegativity of the original selected form.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/OverlapShiftCertificates.lean, exact declaration ConnesGreen.canonical_selected_form_ge_overlap_shift, compiling local source d80c1a8e4c7f0442e092ecaaf726d7aa26822229. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_selected_form_ge_overlap_shift (R T : ℝ) (hT : 0 < T) (hTR : T ≤ R)
    (S : Finset CriticalZeros) (x : Physical T) :
    -arithmeticOverlapShift R * ‖x‖ ^ 2 ≤
      ‖(canonicalPositiveSynthesis T hT).adjoint x‖ ^ 2 - ‖(canonicalSelectedSynthesis T hT S).adjoint x‖ ^ 2 := by sorry
