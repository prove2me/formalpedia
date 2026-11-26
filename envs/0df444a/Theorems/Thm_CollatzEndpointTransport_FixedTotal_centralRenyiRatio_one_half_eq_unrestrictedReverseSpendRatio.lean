-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:46.692428+00:00
-- url     : https://prove2.me/theorems/3c642e15-1648-4731-87fc-e52d150226ee
-- title:
--   Fixed Total: central Renyi Ratio one half eq unrestricted Reverse Spend Ratio
-- statement:
--   The unrestricted reverse-spend ratio is exactly the centered
--   specialization of the cohort reproduction kernel.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L233-L248
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L233-L248

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio
    {theta : ℝ} (htheta : 0 < theta) :
    centralRenyiRatio theta (1 / 2) =
      unrestrictedReverseSpendRatio theta := by sorry
