-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAdmissible_of_window
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiAdmissible_of_window
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:03:36.81817+00:00
-- url     : https://prove2.me/theorems/39754df6-3896-560c-9df1-6c50dad90ab0
-- title:
--   Fixed Total: central Renyi Admissible of window
-- statement:
--   Centrality plus the explicit finite-size hypotheses implies all
--   conditions packaged by `CentralRenyiAdmissible`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L882-L902
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L882-L902

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiAdmissible_of_window
    {N s : ℕ} {theta eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hN : 1 < N)
    (hinterior : (1 / 2 - eta) * N > 1 / 2)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hcen : InCentralRenyiWindow N s eta) :
    CentralRenyiAdmissible N s theta eta := by sorry
