-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberRenyi_le_weighted_by_card
-- name    : CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le_weighted_by_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:46.838841+00:00
-- url     : https://prove2.me/theorems/c6fdb189-b919-47ed-8f01-a8ba048cf368
-- title:
--   Fixed Total: mixed Fiber Renyi le weighted by card
-- statement:
--   Weighted mixture inequality using exact component cardinalities.  Empty
--   components are removed before Jensen's inequality is applied.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L348-L414
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L348-L414

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

theorem CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le_weighted_by_card
    {iota : Type*} {alpha : iota → Type*} {beta : Type*}
    [∀ i, DecidableEq (alpha i)] [DecidableEq beta]
    (U : Finset iota) (W : ∀ i, Finset (alpha i))
    (f : ∀ i, alpha i → beta)
    {B theta : ℝ} (hB : 0 < B) (htheta : 0 < theta)
    (hcards : ∑ i ∈ U, ((W i).card : ℝ) ≤ B) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      ∑ i ∈ activeMixtureIndices U W,
        (((W i).card : ℝ) / B) ^ (-theta) *
          ∑ x ∈ W i,
            ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by sorry
