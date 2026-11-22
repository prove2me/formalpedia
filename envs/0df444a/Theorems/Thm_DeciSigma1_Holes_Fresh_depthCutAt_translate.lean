-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_translate
-- name    : DeciSigma1.Holes.Fresh.depthCutAt_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:02.580729+00:00
-- url     : https://prove2.me/theorems/b3e9b94b-07ad-4adb-a081-058aca6aa61e
-- title:
--   Fresh: depth Cut At translate
-- statement:
--   Enumerating cuts from the right commutes with translating an interval to `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L471-L480
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L471-L480

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}

theorem DeciSigma1.Holes.Fresh.depthCutAt_translate {A : Finset ℕ} {s e : ℕ} (hse : s < e)
    (he : e ∈ A) (hs : s = 0 ∨ s ∈ A) {d : ℕ} (hd : d ≤ anchorCount A s e) :
    depthCutAt A e d = s + depthCutAt (relativeCuts A s e) (e - s) d := by sorry
