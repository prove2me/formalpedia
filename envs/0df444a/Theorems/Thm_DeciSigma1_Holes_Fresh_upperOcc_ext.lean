-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_ext
-- name    : DeciSigma1.Holes.Fresh.upperOcc_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:37.138808+00:00
-- url     : https://prove2.me/theorems/1ed80ac2-5a31-49a6-9a3a-11e90a9f480b
-- title:
--   Fresh: upper Occ ext
-- statement:
--   An upper occurrence is determined by its word and its end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L435-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L435-L445

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.upperOcc_ext {W : Fin k → List α} {t : ℕ} {o o' : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) (ho' : o' ∈ upperOccurrences W t) (h1 : o.1 = o'.1)
        (h2 : o.2.2 = o'.2.2) :
    o = o' := by sorry
