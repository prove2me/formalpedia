-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_add_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:50.479932+00:00
-- url     : https://prove2.me/theorems/ca315715-5348-4188-b767-b9e752a1270a
-- title:
--   Fixed Total: sum rpow one add le
-- statement:
--   The Fixed Total construction uses the sum rpow one add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L33-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L33-L45

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le
    {ι : Type*} (U : Finset ι) (a : ι → ℕ)
    {theta : ℝ} (htheta : 0 < theta) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) ^ (1 + theta) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ((a i : ℝ) ^ (1 + theta)) := by sorry
