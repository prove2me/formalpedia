-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_certificate_above_overlap_shift
-- name    : ConnesGreen.canonical_finite_certificate_above_overlap_shift
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:47:10.169456+00:00
-- url     : https://prove2.me/theorems/69ad3632-1c3c-49d6-96b1-ef140614ac2f
-- title:
--   Construct exact full-tail selected certificates above the improved arithmetic shift
-- statement:
--   Let $0<T\le R$, let $S$ be a finite packet of ACTUAL zeta-zero indices, and choose a single accuracy $\delta>K_R$ and an independent positive tolerance $\varepsilon$. Then there exists a finite ACTUAL zero cutoff $F$ containing $S$, closed under the ORIGINAL zero reflection, such that $$\sum_{\rho\notin F}\|p_{T,\rho}\|^2<\min(\varepsilon,\delta-K_R),\qquad 0\le D_{T,S,F}(\delta).$$ Here the sum is the COMPLETE omitted original positive-column energy and $D$ is the existing selected coefficient correction with its original positive-coefficient inverse. The selected negative packet, physical window and accuracy are unchanged. This CONSTRUCTS a certificate only ABOVE an explicit nonnegative arithmetic shift; it does not prove certificates at every positive accuracy or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/OverlapShiftCertificates.lean, exact declaration ConnesGreen.canonical_finite_certificate_above_overlap_shift, compiling local source d80c1a8e4c7f0442e092ecaaf726d7aa26822229. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_finite_certificate_above_overlap_shift
    (R T : ℝ) (hT : 0 < T) (hTR : T ≤ R) (S : Finset CriticalZeros)
    (δ ε : ℝ) (hδ : arithmeticOverlapShift R < δ) (hε : 0 < ε) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed T (actualGreenSource τ)) ρ.1‖ ^ 2) <
          min ε (δ-arithmeticOverlapShift R) ∧
      0 ≤ canonicalFiniteSelectedCorrection T hT S F δ := by sorry
