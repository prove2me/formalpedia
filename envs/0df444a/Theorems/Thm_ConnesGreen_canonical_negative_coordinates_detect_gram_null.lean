-- Prove2me | Theorems.Thm_ConnesGreen_canonical_negative_coordinates_detect_gram_null
-- name    : ConnesGreen.canonical_negative_coordinates_detect_gram_null
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T20:04:39.025574+00:00
-- url     : https://prove2.me/theorems/f956fe02-baf6-4586-bb28-72bfba2edb69
-- title:
--   Positive-error certificate kernels have no physical directions invisible to selected negative analysis
-- statement:
--   For the SAME original Connes integral Gram matrix $H$, original certificate $K_\delta$ and tagged actors, assume $\delta>0$ and $K_\delta c=0$. Then vanishing of EVERY ORIGINAL selected-negative Gram coordinate $$(Hc)_{\mathrm{inr}\,\rho}=0\quad(\rho\in S)$$ is equivalent to $Hc=0$. Thus selected-negative analysis detects precisely physically zero reconstructions on the certificate kernel. This concerns NEGATIVE analysis, not uniqueness of omitted POSITIVE actual sampling rows. Original data and actor custody are unchanged.
-- source:
--   monocap-tech/weil, compiling source c3e7b782afd23ef5076a93915265a6584646b5e7, exact declaration ConnesGreen.canonical_negative_coordinates_detect_gram_null

import Definitions.Def_ConnesGreen_integral_sampling_row
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

theorem ConnesGreen.canonical_negative_coordinates_detect_gram_null
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ)
    (c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ)
    (hc : canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0) :
    (∀ ρ : {ρ : CriticalZeros // ρ ∈ S},
      (canonicalFiniteColumnKernel t S F *ᵥ c) (Sum.inr ρ) = 0) ↔
      canonicalFiniteColumnKernel t S F *ᵥ c = 0 := by sorry
