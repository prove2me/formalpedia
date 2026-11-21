-- Prove2me | Theorems.Thm_Champernowne_pow_champM_le
-- name    : Champernowne.pow_champM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:24.968912+00:00
-- url     : https://prove2.me/theorems/2e37f461-6cd0-4ec2-b24b-6517bce61c5c
-- title:
--   Champernowne: pow champ M le
-- statement:
--   The Champernowne construction uses the pow champ M le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L31-L34
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L31-L34

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

theorem Champernowne.pow_champM_le (b n : ℕ) :
    b ^ (champM b n - 1) ≤ champIndex b n + 1 := by sorry
