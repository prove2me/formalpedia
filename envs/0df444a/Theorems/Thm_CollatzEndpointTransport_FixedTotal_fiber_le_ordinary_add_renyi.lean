-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fiber_le_ordinary_add_renyi
-- name    : CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_renyi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:26.401476+00:00
-- url     : https://prove2.me/theorems/53df6915-1509-5d88-88eb-a6925252d684
-- title:
--   Fixed Total: fiber le ordinary add renyi
-- statement:
--   Pointwise higher-Renyi split at reference range `R`, source mass `N`,
--   and normalized overload threshold `Q`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L1105-L1139
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L1105-L1139

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_renyi
    {Q N R f theta : ℝ}
    (hQ : 0 < Q) (hN : 0 < N) (hR : 0 < R)
    (hf : 0 ≤ f) (htheta : 0 < theta) :
    f ≤ Q * N / R +
      Q ^ (-theta) * (R / N) ^ theta * f ^ (1 + theta) := by sorry
