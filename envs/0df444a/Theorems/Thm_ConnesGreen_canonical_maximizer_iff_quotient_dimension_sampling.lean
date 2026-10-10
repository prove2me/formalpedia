-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_iff_quotient_dimension_sampling
-- name    : ConnesGreen.canonical_maximizer_iff_quotient_dimension_sampling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T18:23:31.612734+00:00
-- url     : https://prove2.me/theorems/280a4705-8461-4490-b5d9-1c1950d05c5a
-- title:
--   Original finite-profile maximizers admit quotient-dimension bounded actual sampling
-- statement:
--   At nonzero ORIGINAL sharp loss $\mu$, ONE finite ACTUAL sampling set $G$ outside the original cutoff satisfies $$|G|\le\dim\ker K_\mu-\dim\ker H.$$ A NONZERO original physical maximizer with original positive analysis supported in $F$ exists iff finite coefficients satisfy $Hc\ne0$, $K_\mu c=0$ and original integral row vanishing for every index in $G$. The same $G$ is chosen before coefficients. This removes physically zero coefficient directions from the sampling bound; it does not prove existence, sampling uniqueness, a full endpoint certificate, or RH.
-- source:
--   monocap-tech/weil, compiling source 2aef23a3fe056f7d73b4b52a6baf35b6453d9b0b, exact declaration ConnesGreen.canonical_maximizer_iff_quotient_dimension_sampling

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_modulo_gram_kernel
import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_maximizer_iff_quotient_dimension_sampling
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F
        (canonicalCertificateThreshold t ht S)).mulVecLin) -
      Module.finrank ℂ (LinearMap.ker (canonicalFiniteColumnKernel t S F).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by sorry
