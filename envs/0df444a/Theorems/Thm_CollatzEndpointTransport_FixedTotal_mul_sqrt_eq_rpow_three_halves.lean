-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mul_sqrt_eq_rpow_three_halves
-- name    : CollatzEndpointTransport.FixedTotal.mul_sqrt_eq_rpow_three_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:10.580306+00:00
-- url     : https://prove2.me/theorems/fae078ea-71aa-51e6-bc57-16cf80c3820b
-- title:
--   Fixed Total: mul sqrt eq rpow three halves
-- statement:
--   The Fixed Total construction uses the mul sqrt eq rpow three halves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L33-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L33-L45

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.mul_sqrt_eq_rpow_three_halves
    (x : ℝ) (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ ((3 : ℝ) / 2) := by sorry
