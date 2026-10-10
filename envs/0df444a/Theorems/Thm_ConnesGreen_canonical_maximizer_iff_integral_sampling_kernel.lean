-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
-- name    : ConnesGreen.canonical_maximizer_iff_integral_sampling_kernel
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T16:32:54.074975+00:00
-- url     : https://prove2.me/theorems/c20fe037-bad8-4d3c-ad36-15d65463ec5e
-- title:
--   Finitely supported actual maximizers exactly correspond to the original integral sampling kernel
-- statement:
--   Fix the ORIGINAL physical window, actual selected packet $S$, actual cutoff $F$, and nonzero original sharp loss $\mu$. Let $a_i$ be the existing tagged original positive $F$ columns and negative $S$ columns, $H$ their existing explicit integral Gram matrix, and $K_\mu=\mu H+HJH$ the existing integral certificate matrix, with $J=\operatorname{diag}(+1,-1)$ in that original tagging. There exists a NONZERO original maximizing physical vector whose original positive coefficients vanish outside $F$ if and only if there exists a FINITE coefficient vector $c$ such that $$Hc\ne0,\qquad K_\mu c=0,\qquad R_\rho c=0\ \ (\rho\notin F).$$ Every $R_\rho$ is the EXACT original integral positive sampling row, with its original pair signs, actual zero index and multiplicities. The condition $Hc\ne0$ excludes coefficients representing the zero physical vector when tagged columns are dependent. This characterizes ONE finitely supported maximizer, not existence of an endpoint certificate.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/IntegralSamplingKernel.lean, exact declaration ConnesGreen.canonical_maximizer_iff_integral_sampling_kernel, compiling source 48882853479eb428c22a78c8af8eca8c683883d7

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Definitions.Def_ConnesGreen_integral_certificate_kernel

import Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
import Theorems.Thm_ConnesGreen_canonical_maximizer_mem_finite_actor_span
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative

theorem ConnesGreen.canonical_maximizer_iff_integral_sampling_kernel
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) :
    (∃ x : Physical t, x ≠ 0 ∧ x ∈ canonicalMaximizingSpace t ht S ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) ↔
    (∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
      canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        (∑ j, (Sum.elim
          (fun σ : {σ : CriticalZeros // σ ∈ F} => canonicalPairGramKernel t 1 1 ρ σ.1)
          (fun σ : {σ : CriticalZeros // σ ∈ S} => canonicalPairGramKernel t 1 (-1) ρ σ.1) j) * c j) = 0) := by sorry
