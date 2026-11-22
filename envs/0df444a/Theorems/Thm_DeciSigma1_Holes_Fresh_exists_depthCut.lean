-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_exists_depthCut
-- name    : DeciSigma1.Holes.Fresh.exists_depthCut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:20.862802+00:00
-- url     : https://prove2.me/theorems/de6525e9-c2fa-44c4-9180-2b9e93c19d2f
-- title:
--   Fresh: exists depth Cut
-- statement:
--   The depth enumeration hits every anchor in the upper interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L682-L704
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Bound.lean#L682-L704

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

theorem DeciSigma1.Holes.Fresh.exists_depthCut {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) {q : ℕ} (hq : q ∈ anchors W t o.1)
    (hsq : o.2.1 < q) (hqe : q ≤ o.2.2) :
    ∃ d < lowerBlockCount W t o, depthCut W t o d = q := by sorry
