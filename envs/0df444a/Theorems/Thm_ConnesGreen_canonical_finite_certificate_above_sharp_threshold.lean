-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_certificate_above_sharp_threshold
-- name    : ConnesGreen.canonical_finite_certificate_above_sharp_threshold
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T04:19:06.838854+00:00
-- url     : https://prove2.me/theorems/bd30e71b-ace2-4db6-8b7f-0fa8f4be203e
-- title:
--   Exact original full-tail certificates above the sharp selected loss
-- statement:
--   For an ORIGINAL positive physical window $t$ and finite ACTUAL zero packet $S$, let $\mu_{t,S}$ be the supremum of the unchanged selected Rayleigh losses. For EVERY $\delta>\mu_{t,S}$ and independent $\varepsilon>0$, there is a finite ACTUAL zero cutoff $F$ containing $S$, closed under original zero reflection, such that $$\sum_{\rho\notin F}\|p_{t,\rho}\|^2<\min(\varepsilon,\delta-\mu_{t,S}),\qquad D_{t,S,F}(\delta)\ge0.$$ The complete original positive tail is paid from the EXACT gap, on every vector of the completed physical carrier. The physical window, selected packet and accuracy are unchanged. No zero-threshold or RH claim is made.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/SharpCertificateThreshold.lean, exact declaration ConnesGreen.canonical_finite_certificate_above_sharp_threshold, compiling source 9d3b6d1e5542440726233de5981abcdaa263ba8f

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_finite_certificate_above_sharp_threshold
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (δ ε : ℝ)
    (hδ : canonicalCertificateThreshold t ht S < δ) (hε : 0 < ε) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) <
          min ε (δ-canonicalCertificateThreshold t ht S) ∧
      0 ≤ canonicalFiniteSelectedCorrection t ht S F δ := by sorry
