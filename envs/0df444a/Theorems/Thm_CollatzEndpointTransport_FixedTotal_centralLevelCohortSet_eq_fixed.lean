-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_fixed
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_eq_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:36.066617+00:00
-- url     : https://prove2.me/theorems/213b32f1-df80-438a-a3e3-3a1ef68f17ea
-- title:
--   Fixed Total: central Level Cohort Set eq fixed
-- statement:
--   The Fixed Total construction uses the central Level Cohort Set eq fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L311-L316
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L311-L316

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable

theorem CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_eq_fixed
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (h : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta) :
    centralLevelCohortSet M s theta eta u =
      fixedSet (M - (u : ℕ)) s := by sorry
