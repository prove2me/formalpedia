-- Prove2me | Theorems.Thm_ErdosRubinTaylor_core_dc
-- name    : ErdosRubinTaylor.core_dc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:36:57.407306+00:00
-- url     : https://prove2.me/theorems/89d39752-34df-4fdb-b489-0283835b87e8
-- title:
--   Erdos Rubin Taylor: core dc
-- statement:
--   A 2-connected vertex set (of size at least three) inducing neither a complete graph nor an
--   odd cycle is degree-choosable.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTChoosable.lean#L55-L157
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTChoosable.lean#L55-L157

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_BrooksLib_Brooks
public import Definitions.Def_ChoosabilityLib_ERTChoosable
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]

theorem ErdosRubinTaylor.core_dc {C : Type*} [Nonempty C] (G : SimpleGraph V) (S : Set V)
    (h3 : 3 ≤ S.ncard) (h2 : ∀ x ∈ S, (G.induce (S \ {x})).Connected)
    (hK : ¬ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)
    (hC : ∀ n, Odd n → IsEmpty (G.induce S ≃g cycleGraph n)) : DCIn C G S := by sorry
