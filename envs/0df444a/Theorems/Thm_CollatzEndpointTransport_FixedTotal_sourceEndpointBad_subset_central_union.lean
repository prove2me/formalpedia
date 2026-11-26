-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_subset_central_union
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_subset_central_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:19.883055+00:00
-- url     : https://prove2.me/theorems/22cc426c-ae07-49ce-9f3d-685e6da4d236
-- title:
--   Fixed Total: source Endpoint Bad subset central union
-- statement:
--   The Fixed Total construction uses the source Endpoint Bad subset central union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L454-L467
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L454-L467

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_subset_central_union
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    sourceEndpointBad S M ⊆
      centralDiscardedSourceSet M theta eta ∪
        centralSourceEndpointBad S M theta eta := by sorry
