-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_period_le_of_periodicFrom
-- name    : DeciSigma1.Words.Ray.period_le_of_periodicFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:57.692678+00:00
-- url     : https://prove2.me/theorems/303ecea4-e432-478f-9915-90cd61480f26
-- title:
--   Ray: period le of periodic From
-- statement:
--   The period of a ray is at most any positive period of any of its suffixes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L528-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L528-L532

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

theorem DeciSigma1.Words.Ray.period_le_of_periodicFrom {Ω : Ray α} {A p : ℕ} (hp : 0 < p)
    (h : PeriodicFrom Ω.stream A p) :
    Ω.period ≤ p := by sorry
