-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_iff_kernel_dimension_sampling
-- name    : ConnesGreen.canonical_maximizer_iff_kernel_dimension_sampling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:32:55.445481+00:00
-- url     : https://prove2.me/theorems/1814fd0b-e468-4028-952b-602f2bdf0fd3
-- title:
--   Original finitely supported maximizers admit kernel-dimension bounded actual sampling
-- statement:
--   At nonzero original sharp loss $\mu$, there exists ONE finite ACTUAL omitted sampling set $G$ with $|G|\le\dim\ker K_\mu$, chosen before coefficients, such that a NONZERO original physical maximizer whose original positive analysis is supported in $F$ exists iff $Hc\ne0$, $K_\mu c=0$ and every original integral row in $G$ annihilates $c$. Here $H$ and $K_\mu$ are unchanged original integral matrices; dependent actors are allowed. This strengthens the ambient coefficient-count bound and does not prove existence, sampling uniqueness, a full endpoint certificate or RH.
-- source:
--   monocap-tech/weil, compiling source ae5ede91582c6434b1676f98d416b23316942daa, exact declaration ConnesGreen.canonical_maximizer_iff_kernel_dimension_sampling

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_on_certificate_kernel
import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_maximizer_iff_kernel_dimension_sampling
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    ∃ G : Finset CriticalZeros, G.card ≤ Module.finrank ℂ
      (LinearMap.ker (canonicalFiniteIntegralCertificate t S F
        (canonicalCertificateThreshold t ht S)).mulVecLin) ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by sorry
