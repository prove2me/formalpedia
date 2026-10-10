-- Prove2me | Theorems.Thm_ConnesGreen_canonical_gram_null_sampling_custody
-- name    : ConnesGreen.canonical_gram_null_sampling_custody
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T18:17:29.65431+00:00
-- url     : https://prove2.me/theorems/db931273-0c4d-4e03-9104-a985be30cb73
-- title:
--   Original Gram null directions lie in certificate kernels and vanish on every actual sampling row
-- statement:
--   For the EXISTING original integral Gram matrix $H$, original certificate polynomial $K_\delta=\delta H+HJH$, and exact original ACTUAL-positive integral sampling rows, prove BOTH $$\ker H\subseteq\ker K_\delta$$ and $$Hc=0\Longrightarrow R_\rho c=0\quad\text{for EVERY actual zero }\rho.$$ The physical window is positive and $\delta$ is any real. Repeated/dependent tagged actors are allowed. Gram-null coefficients reconstruct the zero ORIGINAL physical vector. Original multiplicities, signs, rows, packet and carrier are preserved.
-- source:
--   monocap-tech/weil, compiling source 2aef23a3fe056f7d73b4b52a6baf35b6453d9b0b, exact declaration ConnesGreen.canonical_gram_null_sampling_custody

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_gram_null_sampling_custody
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) :
    (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin ≤
      LinearMap.ker (canonicalFiniteIntegralCertificate t S F δ).mulVecLin) ∧
    (∀ (ρ : CriticalZeros)
      (c : ({σ : CriticalZeros // σ ∈ F} ⊕ {σ : CriticalZeros // σ ∈ S}) → ℂ),
      canonicalFiniteColumnKernel t S F *ᵥ c = 0 →
      canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by sorry
