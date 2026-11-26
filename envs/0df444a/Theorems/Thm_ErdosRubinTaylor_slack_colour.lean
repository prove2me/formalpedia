-- Prove2me | Theorems.Thm_ErdosRubinTaylor_slack_colour
-- name    : ErdosRubinTaylor.slack_colour
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:30:07.051972+00:00
-- url     : https://prove2.me/theorems/e5f010ae-2c12-459d-9e77-64b8b2cc7987
-- title:
--   Erdos Rubin Taylor: slack colour
-- statement:
--   **Lemma A (slack).** If `T` is connected, every vertex of `T` has at least as many colours
--   as neighbours in `T`, and some vertex has more, then `T` is colourable from the lists.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L287-L328
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L287-L328

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

theorem ErdosRubinTaylor.slack_colour {C : Type*} [Nonempty C] (G : SimpleGraph V) (T : Set V)
    (hT : SConn G T) {w0 : V} (hw0 : w0 ∈ T) (L : V → Finset C)
    (hL : ∀ v ∈ T, dIn G T v ≤ (L v).card) (hw : dIn G T w0 < (L w0).card) :
    ColIn G T L := by sorry
