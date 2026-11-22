-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_onset_le_of_periodicFrom
-- name    : DeciSigma1.Words.Ray.onset_le_of_periodicFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:56.8961+00:00
-- url     : https://prove2.me/theorems/4fa32995-c615-4c6f-86f7-d770c6f20fdb
-- title:
--   Ray: onset le of periodic From
-- statement:
--   A suffix that is purely periodic with any positive period starts at or after the onset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L404-L415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L404-L415

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

theorem DeciSigma1.Words.Ray.onset_le_of_periodicFrom {A p : ℕ} (hp : 0 < p) (h : PeriodicFrom Ω.stream A p) :
    Ω.onset ≤ A := by sorry
