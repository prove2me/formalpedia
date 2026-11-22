-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_onset_eq_of_stream_eq
-- name    : DeciSigma1.Words.Ray.onset_eq_of_stream_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:56.208508+00:00
-- url     : https://prove2.me/theorems/7e384230-edb2-4f00-8330-acee16aa96eb
-- title:
--   Ray: onset eq of stream eq
-- statement:
--   Rays with the same infinite word have the same onset.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L520-L525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L520-L525

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

theorem DeciSigma1.Words.Ray.onset_eq_of_stream_eq {Ω Ω' : Ray α} (h : ∀ t, Ω.stream t = Ω'.stream t) :
    Ω.onset = Ω'.onset := by sorry
