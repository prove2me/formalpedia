-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_activeMixtureIndices_subset
-- name    : CollatzEndpointTransport.FixedTotal.activeMixtureIndices_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:25.543783+00:00
-- url     : https://prove2.me/theorems/da1ad942-4f6a-5c42-91b3-175ac8a63aa9
-- title:
--   Fixed Total: active Mixture Indices subset
-- statement:
--   The Fixed Total construction uses the active Mixture Indices subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L339-L344
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L339-L344

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

theorem CollatzEndpointTransport.FixedTotal.activeMixtureIndices_subset
    {iota : Type*} {alpha : iota → Type*}
    (U : Finset iota) (W : ∀ i, Finset (alpha i)) :
    activeMixtureIndices U W ⊆ U := by sorry
