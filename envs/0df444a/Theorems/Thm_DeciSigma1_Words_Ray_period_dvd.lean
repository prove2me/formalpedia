-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_period_dvd
-- name    : DeciSigma1.Words.Ray.period_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:55.060705+00:00
-- url     : https://prove2.me/theorems/93eaa565-c0ff-4c8e-aa03-654a11696da8
-- title:
--   Ray: period dvd
-- statement:
--   The Ray construction uses the period dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L441-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L441-L442

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

theorem DeciSigma1.Words.Ray.period_dvd : Ω.period ∣ Ω.loop.length := by sorry
