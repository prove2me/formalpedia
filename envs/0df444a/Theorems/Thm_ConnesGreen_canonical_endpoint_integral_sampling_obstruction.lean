-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_integral_sampling_obstruction
-- name    : ConnesGreen.canonical_endpoint_integral_sampling_obstruction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T16:42:08.689738+00:00
-- url     : https://prove2.me/theorems/dca1283a-1dfe-4e23-8299-f7fdcd39c922
-- title:
--   Positive endpoint certificates force a nontrivial original integral sampling kernel
-- statement:
--   At POSITIVE original sharp loss $\mu>0$, a nonnegative ORIGINAL finite selected correction at EXACT accuracy $\delta=\mu$ and cutoff $F$ forces finite coefficients $c$ with $$Hc\ne0,\qquad K_\mu c=0,\qquad R_\rho c=0\ \ (\rho\notin F).$$ Here $H$, $K_\mu$ and every omitted $R_\rho$ are the existing original integral Gram/certificate/sampling kernels, with actual zeta-zero indices and analytic multiplicities, original reflection-pair normalization, and unchanged selected packet. The SAME $F$ is preserved. The infinitely many omitted rows remain explicit; one such finite coefficient vector is not claimed sufficient for a certificate.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/IntegralSamplingKernel.lean, exact declaration ConnesGreen.canonical_endpoint_integral_sampling_obstruction, compiling source 48882853479eb428c22a78c8af8eca8c683883d7

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Definitions.Def_ConnesGreen_integral_certificate_kernel

import Theorems.Thm_ConnesGreen_canonical_maximizer_iff_integral_sampling_kernel
import Theorems.Thm_ConnesGreen_canonical_positive_threshold_attained
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative

theorem ConnesGreen.canonical_endpoint_integral_sampling_obstruction
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) :
    ∃ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteColumnKernel t S F *ᵥ c ≠ 0 ∧
      canonicalFiniteIntegralCertificate t S F (canonicalCertificateThreshold t ht S) *ᵥ c = 0 ∧
      ∀ ρ : CriticalZeros, ρ ∉ F →
        (∑ j, (Sum.elim
          (fun σ : {σ : CriticalZeros // σ ∈ F} => canonicalPairGramKernel t 1 1 ρ σ.1)
          (fun σ : {σ : CriticalZeros // σ ∈ S} => canonicalPairGramKernel t 1 (-1) ρ σ.1) j) * c j) = 0 := by sorry
