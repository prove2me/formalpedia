-- Prove2me | Theorems.Thm_Champernowne_champM_pos
-- name    : Champernowne.champM_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:08.405154+00:00
-- url     : https://prove2.me/theorems/f1b8c311-ab8d-4dba-9f8d-80fc52c55b47
-- title:
--   Champernowne: champ M pos
-- statement:
--   The Champernowne construction uses the champ M pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L29-L29
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L29-L29

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology

theorem Champernowne.champM_pos (b n : ℕ) : 0 < champM b n := by sorry
