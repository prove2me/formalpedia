-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberCard_eq_sigmaFiber
-- name    : CollatzEndpointTransport.FixedTotal.mixedFiberCard_eq_sigmaFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:39.354311+00:00
-- url     : https://prove2.me/theorems/02b768f2-edcf-49ae-b41b-684dc368b779
-- title:
--   Fixed Total: mixed Fiber Card eq sigma Fiber
-- statement:
--   A mixed fiber is the fiber of the corresponding sigma source.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L92-L104
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L92-L104

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

theorem CollatzEndpointTransport.FixedTotal.mixedFiberCard_eq_sigmaFiber
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) (b : β) :
    mixedFiberCard U W f b =
      (mapFiber (U.sigma W) (fun p => f p.1 p.2) b).card := by sorry
