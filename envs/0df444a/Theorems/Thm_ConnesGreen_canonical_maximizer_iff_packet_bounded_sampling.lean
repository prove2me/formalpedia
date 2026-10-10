-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_iff_packet_bounded_sampling
-- name    : ConnesGreen.canonical_maximizer_iff_packet_bounded_sampling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T20:14:31.523993+00:00
-- url     : https://prove2.me/theorems/9bb471a0-9abc-497e-a98c-e4e211d98d2a
-- title:
--   Positive sharp-loss maximizers admit actual sampling bounded by selected packet size
-- statement:
--   At strictly positive ORIGINAL sharp loss $\mu$, ONE finite ACTUAL omitted sampling set $G$ has size at most the ORIGINAL selected packet size $|S|$. A NONZERO original physical maximizing vector with original positive-analysis profile supported in $F$ exists iff finite coefficients satisfy $Hc\ne0$, $K_\mu c=0$ and ORIGINAL integral sampling-row vanishing for every index in $G$. The same set is chosen before coefficients. No maximizer existence, smooth-test attainment, full endpoint certificate, arithmetic injectivity or RH is claimed.
-- source:
--   monocap-tech/weil, compiling source c3e7b782afd23ef5076a93915265a6584646b5e7, exact declaration ConnesGreen.canonical_maximizer_iff_packet_bounded_sampling

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_packet_bound
import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_maximizer_iff_packet_bounded_sampling
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S) :
    ∃ G : Finset CriticalZeros, G.card ≤ S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by sorry
