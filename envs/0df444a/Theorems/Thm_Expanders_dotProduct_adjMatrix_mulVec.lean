-- Prove2me | Theorems.Thm_Expanders_dotProduct_adjMatrix_mulVec
-- name    : Expanders.dotProduct_adjMatrix_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:08:42.8548+00:00
-- url     : https://prove2.me/theorems/1d0360f4-b149-4faf-a44c-857780e64891
-- title:
--   Expanders: dot Product adj Matrix mul Vec
-- statement:
--   The Expanders construction uses the dot Product adj Matrix mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L62-L64
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L62-L64

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.dotProduct_adjMatrix_mulVec (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℝ) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = ∑ v, x v * ∑ w ∈ G.neighborFinset v, y w := by sorry
