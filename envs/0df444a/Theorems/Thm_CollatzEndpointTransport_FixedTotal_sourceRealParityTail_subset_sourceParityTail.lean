-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceRealParityTail_subset_sourceParityTail
-- name    : CollatzEndpointTransport.FixedTotal.sourceRealParityTail_subset_sourceParityTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:51.030714+00:00
-- url     : https://prove2.me/theorems/c2dd1865-2cd8-4011-b812-351302e22a60
-- title:
--   Fixed Total: source Real Parity Tail subset source Parity Tail
-- statement:
--   A real deviation by `t M` lies in the exact cutoff tail at tolerance
--   `t/2`; the loss absorbs the two integer cutoff boundaries.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L787-L823
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L787-L823

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

theorem CollatzEndpointTransport.FixedTotal.sourceRealParityTail_subset_sourceParityTail
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (htM : 2 ≤ t * M) :
    sourceRealParityTail M t ⊆ sourceParityTail M (t / 2) := by sorry
