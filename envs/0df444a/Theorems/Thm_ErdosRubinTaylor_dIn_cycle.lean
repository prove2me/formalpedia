-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_cycle
-- name    : ErdosRubinTaylor.dIn_cycle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:31:30.906895+00:00
-- url     : https://prove2.me/theorems/0a521e88-bb31-470d-8dcc-a8ffd42d56d9
-- title:
--   Erdos Rubin Taylor: d In cycle
-- statement:
--   The Erdos Rubin Taylor construction uses the d In cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L212-L218
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L212-L218

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

theorem ErdosRubinTaylor.dIn_cycle {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) (hn : Odd n)
    (h2 : 2 ≤ T.ncard) {u : V} (hu : u ∈ T) : dIn G T u = 2 := by sorry
