-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_onset_le_stem
-- name    : DeciSigma1.Words.Ray.onset_le_stem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:55.250752+00:00
-- url     : https://prove2.me/theorems/cef6fdb3-71d9-4522-8528-8c56de1ce84f
-- title:
--   Ray: onset le stem
-- statement:
--   The Ray construction uses the onset le stem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L393-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L393-L394

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]

theorem DeciSigma1.Words.Ray.onset_le_stem : Ω.onset ≤ Ω.stem.length := by sorry
