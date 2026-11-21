-- Prove2me | Theorems.Thm_Champernowne_le_pow_champM
-- name    : Champernowne.le_pow_champM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:20.161676+00:00
-- url     : https://prove2.me/theorems/d55754c1-2a12-4d39-8969-5a63561c13fe
-- title:
--   Champernowne: le pow champ M
-- statement:
--   The Champernowne construction uses the le pow champ M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L36-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean#L36-L38

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

theorem Champernowne.le_pow_champM {b : ℕ} (hb : 1 < b) (n : ℕ) :
    champIndex b n + 1 ≤ b ^ champM b n := by sorry
