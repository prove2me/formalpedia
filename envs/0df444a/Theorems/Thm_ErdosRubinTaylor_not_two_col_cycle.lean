-- Prove2me | Theorems.Thm_ErdosRubinTaylor_not_two_col_cycle
-- name    : ErdosRubinTaylor.not_two_col_cycle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:34:46.880718+00:00
-- url     : https://prove2.me/theorems/9c989d2e-4e73-53fc-b64e-ac0709218bc7
-- title:
--   Erdos Rubin Taylor: not two col cycle
-- statement:
--   The Erdos Rubin Taylor construction uses the not two col cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L228-L243
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L228-L243

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
omit [Fintype V]

theorem ErdosRubinTaylor.not_two_col_cycle [Finite V] {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) (hn : Odd n)
    (h2 : 2 ≤ T.ncard) (f : V → ℕ) (hf1 : ∀ v ∈ T, f v ∈ ({0, 1} : Finset ℕ))
    (hf2 : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → f u ≠ f v) : False := by sorry
