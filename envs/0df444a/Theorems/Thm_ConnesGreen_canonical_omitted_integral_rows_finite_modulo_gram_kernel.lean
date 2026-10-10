-- Prove2me | Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_modulo_gram_kernel
-- name    : ConnesGreen.canonical_omitted_integral_rows_finite_modulo_gram_kernel
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T18:20:46.493979+00:00
-- url     : https://prove2.me/theorems/2df88f8e-13d6-4152-a978-8bff928d3315
-- title:
--   Actual omitted integral sampling needs only the physical certificate quotient dimension
-- statement:
--   For the ORIGINAL integral Gram and certificate matrices in a positive physical window, ONE finite set $G$ of ACTUAL omitted zero indices outside the SAME $F$ satisfies $$|G|\le\dim\ker K_\delta-\dim\ker H.$$ For EVERY coefficient $c$ in the original certificate kernel, vanishing of original integral rows in $G$ is equivalent to vanishing of EVERY original omitted row. The difference is exactly the quotient dimension after removing original Gram-null coefficient directions. Actual index and actor custody are unchanged. No sampling injectivity, arithmetic lower bound or RH is asserted.
-- source:
--   monocap-tech/weil, compiling source 2aef23a3fe056f7d73b4b52a6baf35b6453d9b0b, exact declaration ConnesGreen.canonical_omitted_integral_rows_finite_modulo_gram_kernel

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_on_matrix_kernel_modulo
import Theorems.Thm_ConnesGreen_canonical_gram_null_sampling_custody
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_omitted_integral_rows_finite_modulo_gram_kernel
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) -
      Module.finrank ℂ (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by sorry
