-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_kappa_mul_cq_mul
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.kappa_mul_cq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:30.20084+00:00
-- url     : https://prove2.me/theorems/61360fad-8459-5481-8268-2322f7281828
-- title:
--   Optimized Linear Pullback: kappa mul cq mul
-- statement:
--   The Optimized Linear Pullback construction uses the kappa mul cq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L175-L180
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L175-L180

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_mul_cq_mul

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.kappa_mul_cq_mul
    {kappa q : ℝ} (hk : 0 < kappa) (hq : 0 < q) :
    kappa * cq kappa q * q =
      (q - QuantitativeDensity.a0) / 4 := by sorry
