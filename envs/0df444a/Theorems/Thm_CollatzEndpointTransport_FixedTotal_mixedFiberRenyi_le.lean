-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberRenyi_le
-- name    : CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:52.427576+00:00
-- url     : https://prove2.me/theorems/d8ddf6db-df42-5f56-bd8d-3b5b3ad9af41
-- title:
--   Fixed Total: mixed Fiber Renyi le
-- statement:
--   Combined `(1+theta)` endpoint-fiber moment of a finite family.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L98-L128
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L98-L128

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ∑ x ∈ W i,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by sorry
