-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortRenyiSourceMoment_le_fixed
-- name    : CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_le_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:28.967392+00:00
-- url     : https://prove2.me/theorems/bf44ab26-24ed-4cbf-8d55-df1105a2dd48
-- title:
--   Fixed Total: cohort Renyi Source Moment le fixed
-- statement:
--   Backward-compatible inequality form of the exact Renyi bridge.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L228-L233
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L228-L233

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
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralEndpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_le_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) {theta : ℝ}
    (_htheta : 0 ≤ theta) :
    cohortRenyiSourceMoment M u s theta ≤
      fixedRenyiNumerator (M - (u : ℕ)) s theta := by sorry
