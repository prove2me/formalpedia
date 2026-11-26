-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_noncentral_implies_global_parity_deviation
-- name    : CollatzEndpointTransport.FixedTotal.noncentral_implies_global_parity_deviation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:03.01736+00:00
-- url     : https://prove2.me/theorems/3e2740e9-f83b-5879-95c5-57b6fb0800ac
-- title:
--   Fixed Total: noncentral implies global parity deviation
-- statement:
--   If the first odd letter occurs early, a noncentral fixed-total length
--   forces a proportional deviation of the whole shell odd count.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L906-L951
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L906-L951

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

theorem CollatzEndpointTransport.FixedTotal.noncentral_implies_global_parity_deviation
    {M s K : ℕ} {eta : ℝ}
    (u : Fin M) (huK : (u : ℕ) < K)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 2 ≤ eta * M)
    (hnot : ¬ InCentralRenyiWindow (M - (u : ℕ)) s eta) :
    eta / 2 * M < |(s : ℝ) - (M : ℝ) / 2| := by sorry
