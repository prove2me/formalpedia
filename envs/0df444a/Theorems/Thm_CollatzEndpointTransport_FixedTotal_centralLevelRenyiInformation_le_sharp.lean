-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelRenyiInformation_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelRenyiInformation_le_sharp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:11:39.614151+00:00
-- url     : https://prove2.me/theorems/0b4948b4-30df-4644-9b0d-04031f32b69c
-- title:
--   Fixed Total: central Level Renyi Information le sharp
-- statement:
--   Exact-cardinality weighted mixture at one odd-count level.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L511-L594
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L511-L594

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralLevelRenyiInformation_le_sharp
    {M s : ℕ} {theta eta : ℝ}
    (htheta : 0 < theta) (hsM : s ≤ M) :
    centralLevelRenyiInformation M s theta eta ≤
      (3 : ℝ) ^ theta *
        ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
            (centralLevelCohortSet M s theta eta),
          ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
            fixedRenyiMoment (M - (u : ℕ)) s theta := by sorry
