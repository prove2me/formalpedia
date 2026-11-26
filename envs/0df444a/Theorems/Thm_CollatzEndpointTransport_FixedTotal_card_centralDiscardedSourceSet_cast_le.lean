-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralDiscardedSourceSet_cast_le
-- name    : CollatzEndpointTransport.FixedTotal.card_centralDiscardedSourceSet_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:12.613772+00:00
-- url     : https://prove2.me/theorems/921bf44a-0bf6-59b6-892f-4003d8af93c7
-- title:
--   Fixed Total: card central Discarded Source Set cast le
-- statement:
--   Explicit polynomial-times-exponential cardinal bound for the discarded
--   central source.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L1043-L1079
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L1043-L1079

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

theorem CollatzEndpointTransport.FixedTotal.card_centralDiscardedSourceSet_cast_le
    {M K : ℕ} {theta eta : ℝ}
    (hKM : K ≤ M)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
      ((M + 1) * 2 ^ (M - K) : ℕ) +
        (2 : ℝ) ^ M *
          (2 * Real.exp (-2 * (eta / 4) ^ 2 * M)) := by sorry
