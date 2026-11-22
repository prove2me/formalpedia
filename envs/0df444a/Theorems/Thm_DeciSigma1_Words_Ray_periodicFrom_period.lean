-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_periodicFrom_period
-- name    : DeciSigma1.Words.Ray.periodicFrom_period
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:59.260809+00:00
-- url     : https://prove2.me/theorems/89ca29ca-9b03-40d5-acc8-51913c59091d
-- title:
--   Ray: periodic From period
-- statement:
--   The Ray construction uses the periodic From period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L534-L535
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L534-L535

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

theorem DeciSigma1.Words.Ray.periodicFrom_period (Ω : Ray α) : PeriodicFrom Ω.stream Ω.onset Ω.period := by sorry
