-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
-- name    : ConnesGreen.canonical_finite_certificate_neutral_tail_zero
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T04:18:53.973571+00:00
-- url     : https://prove2.me/theorems/62f47bab-3f62-40fe-9a7c-17e05e57af0b
-- title:
--   A saturated original vector forces every omitted positive column to vanish
-- statement:
--   Let $\delta>0$ and suppose an ORIGINAL finite selected correction $D_{t,S,F}(\delta)$ is nonnegative. If an ORIGINAL physical vector $x$ saturates the FULL shifted selected form, $$\|P_t^*x\|^2-\|N_{t,S}^*x\|^2+\delta\|x\|^2=0,$$ then $$\langle p_{t,\rho},x\rangle=0\quad\text{for EVERY actual zero }\rho\notin F.$$ Thus a finite certificate at a positive sharp endpoint must annihilate its complete omitted analysis tail on every saturated vector. No existence of a saturated vector, endpoint certificate, or sufficiency of this condition alone is asserted.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/SharpCertificateThreshold.lean, exact declaration ConnesGreen.canonical_finite_certificate_neutral_tail_zero, compiling source 9d3b6d1e5542440726233de5981abcdaa263ba8f

import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_finite_certificate_neutral_tail_zero
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F δ)
    (x : Physical t)
    (hneutral : ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 + δ * ‖x‖ ^ 2 = 0) :
    ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by sorry
