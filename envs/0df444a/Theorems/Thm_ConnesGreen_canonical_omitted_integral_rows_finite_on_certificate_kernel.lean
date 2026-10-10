-- Prove2me | Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_on_certificate_kernel
-- name    : ConnesGreen.canonical_omitted_integral_rows_finite_on_certificate_kernel
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:30:38.057843+00:00
-- url     : https://prove2.me/theorems/1fc2af33-ab7b-43f8-a20b-06405c62da86
-- title:
--   Actual omitted integral rows require at most the certificate kernel dimension
-- statement:
--   For the unchanged original Connes integral certificate $K_\delta$, selected actual packet $S$ and cutoff $F$, ONE finite set $G$ of ACTUAL omitted zero indices satisfies $G\cap F=\varnothing$ and $|G|\le\dim\ker K_\delta$. For EVERY coefficient vector in that exact certificate kernel, vanishing of the original integral sampling rows in $G$ is equivalent to vanishing of EVERY original omitted actual row. Any real $\delta$ is allowed. Actual multiplicities, signs and actor custody are preserved. No uniqueness or arithmetic lower bound is asserted.
-- source:
--   monocap-tech/weil, compiling source ae5ede91582c6434b1676f98d416b23316942daa, exact declaration ConnesGreen.canonical_omitted_integral_rows_finite_on_certificate_kernel

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_omitted_integral_rows_finite_on_certificate_kernel
    (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by sorry
