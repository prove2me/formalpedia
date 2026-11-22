-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_fw_overlap
-- name    : DeciSigma1.Holes.Periodic.fw_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:55.672632+00:00
-- url     : https://prove2.me/theorems/15a403fa-3657-4e3f-a864-c80a95b980b6
-- title:
--   Periodic: fw overlap
-- statement:
--   Pieces of different classes with periods `dR ≤ dP` overlap in fewer than `dP + dR` letters
--   (Fine–Wilf).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L412-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L412-L452

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}

theorem DeciSigma1.Holes.Periodic.fw_overlap {W : Fin k → List α} {dP dR : ℕ} (P : Piece W dP) (R : Piece W dR)
    (hcls : ¬ IsConjugate P.root R.root) (hd : dR ≤ dP) (hl : P.coordinate = R.coordinate) :
    min P.stop R.stop - max P.start R.start < dP + dR := by sorry
