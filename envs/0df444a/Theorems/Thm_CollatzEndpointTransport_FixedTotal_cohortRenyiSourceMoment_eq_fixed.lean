-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortRenyiSourceMoment_eq_fixed
-- name    : CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_eq_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:12.173024+00:00
-- url     : https://prove2.me/theorems/0c9f53f0-5b4e-45f9-90a9-a5da3a11c850
-- title:
--   Fixed Total: cohort Renyi Source Moment eq fixed
-- statement:
--   Exact higher-Renyi endpoint-to-correction bridge.  No sign restriction
--   on the exponent is needed because the underlying fibers are equal.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L192-L225
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L192-L225

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

theorem CollatzEndpointTransport.FixedTotal.cohortRenyiSourceMoment_eq_fixed
    (M : ℕ) (u : Fin M) (s : ℕ) (theta : ℝ) :
    cohortRenyiSourceMoment M u s theta =
      fixedRenyiNumerator (M - (u : ℕ)) s theta := by sorry
