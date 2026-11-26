-- Prove2me | Theorems.Thm_ErdosRubinTaylor_cut_decomp
-- name    : ErdosRubinTaylor.cut_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:17.89786+00:00
-- url     : https://prove2.me/theorems/393f9757-6f81-5ae2-a246-0c6522b04960
-- title:
--   Erdos Rubin Taylor: cut decomp
-- statement:
--   Splitting a connected set at a cut vertex `x`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L108-L131
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L108-L131

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.cut_decomp {T : Set V} (hT : SConn G T) {x : V} (hx : x ∈ T)
    (hcut : ¬ SConn G (T \ {x})) (hne : (T \ {x}).Nonempty) :
    ∃ A B : Set V, A ∪ B = T \ {x} ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧ SConn G (insert x A) ∧ SConn G (insert x B) := by sorry
