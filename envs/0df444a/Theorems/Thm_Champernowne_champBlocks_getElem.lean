-- Prove2me | Theorems.Thm_Champernowne_champBlocks_getElem
-- name    : Champernowne.champBlocks_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:21.228436+00:00
-- url     : https://prove2.me/theorems/ada932e2-8fc3-40c2-ab12-d765aeb40e05
-- title:
--   Champernowne: champ Blocks get Elem
-- statement:
--   Coherence: any sufficiently long prefix computes `champDigit`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Prefix.lean#L34-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Prefix.lean#L34-L40

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champBlocks_getElem (b N i : ℕ) (h : i < (champBlocks b N).length) :
    (champBlocks b N)[i] = champDigit b i := by sorry
