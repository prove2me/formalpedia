-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_mul_sqrt_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_mul_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:56:29.808+00:00
-- url     : https://prove2.me/theorems/a592ac9d-e173-4502-ba52-a4c823f433d1
-- title:
--   Fixed Total: sum mul sqrt le
-- statement:
--   The Fixed Total construction uses the sum mul sqrt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L47-L78
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean#L47-L78

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_mul_sqrt_le
    {ι : Type*} (U : Finset ι) (a : ι → ℕ) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ U, a i : ℕ) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, (a i : ℝ) * Real.sqrt (a i) := by sorry
