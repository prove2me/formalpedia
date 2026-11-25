-- Prove2me | Theorems.Thm_Expanders_adjMatrix_dotProduct_comm
-- name    : Expanders.adjMatrix_dotProduct_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:18:46.522864+00:00
-- url     : https://prove2.me/theorems/b65ca8d5-b843-436d-83b6-e006fa59ead9
-- title:
--   Expanders: adj Matrix dot Product comm
-- statement:
--   The Expanders construction uses the adj Matrix dot Product comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/MixingAux.lean#L28-L30
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/MixingAux.lean#L28-L30

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.adjMatrix_dotProduct_comm (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℝ) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = dotProduct y (G.adjMatrix ℝ *ᵥ x) := by sorry
