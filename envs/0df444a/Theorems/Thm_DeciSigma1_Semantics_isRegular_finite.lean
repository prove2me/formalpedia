-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_finite
-- name    : DeciSigma1.Semantics.isRegular_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:40.466123+00:00
-- url     : https://prove2.me/theorems/ef10466c-3b9d-4293-9b43-9c0e7ab0d681
-- title:
--   Semantics: is Regular finite
-- statement:
--   Finite languages are regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L97-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L97-L104

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}

theorem DeciSigma1.Semantics.isRegular_finite {L : Language n} (hf : L.Finite) : IsRegular L := by sorry
