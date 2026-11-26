-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSeparatorProportion_le_piStar
-- name    : CollatzEndpointTransport.FixedTotal.centralSeparatorProportion_le_piStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:27.240812+00:00
-- url     : https://prove2.me/theorems/f5fe54d2-cdbd-54e1-8145-bd93c3e4ed2b
-- title:
--   Fixed Total: central Separator Proportion le pi Star
-- statement:
--   An explicit finite-size condition places every central separator
--   proportion below the fixed interior value `piStar`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1216-L1236
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1216-L1236

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralSeparatorProportion_le_piStar
    {N s : ℕ} {theta eta : ℝ}
    (hN : 1 < N) (hs : 0 < s)
    (hcen : InCentralRenyiWindow N s eta)
    (hsize :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1)) :
    centralSeparatorProportion N s ≤ centralRenyiPiStar theta eta := by sorry
