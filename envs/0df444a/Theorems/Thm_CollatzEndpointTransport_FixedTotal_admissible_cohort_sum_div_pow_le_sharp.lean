-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_admissible_cohort_sum_div_pow_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.admissible_cohort_sum_div_pow_le_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:29.122599+00:00
-- url     : https://prove2.me/theorems/63267985-158b-571c-90dc-ff4c3294feeb
-- title:
--   Fixed Total: admissible cohort sum div pow le sharp
-- statement:
--   One first-odd cohort after exact dyadic normalization.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L757-L811
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L757-L811

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.admissible_cohort_sum_div_pow_le_sharp
    {M : ℕ} (u : Fin M) {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    (∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
        ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta) /
        (2 : ℝ) ^ M ≤
      (((2 : ℝ) ^ (u : ℕ))⁻¹ *
        (centralMomentConstant theta eta *
          (M + 1 : ℝ) ^ (1 + theta))) := by sorry
