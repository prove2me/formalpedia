-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_iff_finite_integral_sampling
-- name    : ConnesGreen.canonical_maximizer_iff_finite_integral_sampling
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:12:02.319274+00:00
-- url     : https://prove2.me/theorems/30c6e807-2c5c-4555-8bb1-095b3fa99bce
-- title:
--   A fixed actual finite sampling set exactly tests finitely supported original maximizers
-- statement:
--   Fix an ORIGINAL positive physical window, selected packet $S$, cutoff $F$ and nonzero original sharp loss $\mu$. There exists ONE finite ACTUAL row set $G$ outside $F$, with $|G|\le|F|+|S|$, such that a NONZERO original maximizing physical vector with original positive-analysis support in $F$ exists if and only if finite coefficients satisfy $$Hc\ne0,\qquad K_\mu c=0,\qquad R_\rho c=0\ (\rho\in G).$$ The existing original integral Gram and certificate matrices are retained, and $Hc\ne0$ excludes zero physical reconstructions in dependent actor families. The SAME $G$ is chosen before the coefficient vector. This characterizes one finitely supported maximizer and does not assert endpoint certificate existence or sampling uniqueness.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteSamplingWitness.lean, exact declaration ConnesGreen.canonical_maximizer_iff_finite_integral_sampling, compiling source a5af8470c9220c0783752dac5c5a25fc842dbe0d

import Definitions.Def_ConnesGreen_integral_sampling_row

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite
import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_maximizer_iff_finite_integral_sampling
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    ∃ G : Finset CriticalZeros, G.card ≤ F.card + S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ((∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
        ∀ ρ : CriticalZeros, ρ ∉ F →
          ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
      (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
        canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
        ∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0)) := by sorry
