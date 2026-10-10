-- Prove2me | Theorems.Thm_ConnesGreen_canonical_maximizer_mem_finite_actor_span
-- name    : ConnesGreen.canonical_maximizer_mem_finite_actor_span
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T13:22:26.167277+00:00
-- url     : https://prove2.me/theorems/d9a663d9-8c7a-40f8-84e1-76ca03046e3c
-- title:
--   Finite maximizing profiles lie in the original finite actor span
-- statement:
--   Fix the original physical support window, selected actual-zero packet $S$, and finite actual-positive cutoff $F$. If the original sharp loss $\mu$ is nonzero and an original maximizing vector $x$ has all its original positive-column coefficients zero outside $F$, then $x$ lies in the finite complex span of the ORIGINAL negative columns indexed by $S$ and ORIGINAL positive columns indexed by $F$. Neither actual zeros nor their multiplicities nor the physical norm is changed. Finite support refers to reflection-pair positive coefficients, not individual Mellin coefficients.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/EndpointFiniteReconstruction.lean, exact declaration ConnesGreen.canonical_maximizer_mem_finite_actor_span, compiling source 5f573c18985ee59bff27315944cd5bb75a488e01

import Definitions.Def_ConnesGreen_positive_endpoint_support

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative

theorem ConnesGreen.canonical_maximizer_mem_finite_actor_span
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : canonicalCertificateThreshold t ht S ≠ 0) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S)
    (hc : ∀ ρ : CriticalZeros, ρ ∉ F →
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    x ∈ Submodule.span ℂ
      (Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ S} =>
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∪
       Set.range (fun ρ : {ρ : CriticalZeros // ρ ∈ F} =>
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)) := by sorry
