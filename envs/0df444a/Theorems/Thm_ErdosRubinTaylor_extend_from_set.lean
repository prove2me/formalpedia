-- Prove2me | Theorems.Thm_ErdosRubinTaylor_extend_from_set
-- name    : ErdosRubinTaylor.extend_from_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:29:50.554378+00:00
-- url     : https://prove2.me/theorems/d41178f9-3ac1-5a38-a04b-4c1ea3ad2a55
-- title:
--   Erdos Rubin Taylor: extend from set
-- statement:
--   **Lemma B (extension).** If `G` is connected and the nonempty vertex set `T` is
--   degree-choosable, then `G` is degree-choosable.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L336-L396
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L336-L396

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]

theorem ErdosRubinTaylor.extend_from_set {C : Type*} [Nonempty C] (G : SimpleGraph V)
    (hconn : G.Connected) (T : Set V) (hTne : T.Nonempty) (hT : DCIn C G T)
    (L : V → Finset C) (hL : ∀ v, dIn G Set.univ v ≤ (L v).card) : ColIn G Set.univ L := by sorry
