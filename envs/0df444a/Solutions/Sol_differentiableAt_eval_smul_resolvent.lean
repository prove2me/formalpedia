-- Prove2me | solution 1 for differentiableAt_eval_smul_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:39.361977+00:00
-- url     : https://prove2.me/submissions/36c92ef1-1707-4d6c-8624-7e6c7bb429ba

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) (p : ℂ[X]) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    DifferentiableAt ℂ (fun w : ℂ => p.eval w • resolvent A w) z :=
  (p.differentiable z).smul (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt
