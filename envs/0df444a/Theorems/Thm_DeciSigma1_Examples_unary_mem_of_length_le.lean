-- Prove2me | Theorems.Thm_DeciSigma1_Examples_unary_mem_of_length_le
-- name    : DeciSigma1.Examples.unary_mem_of_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:43.164779+00:00
-- url     : https://prove2.me/theorems/8fc78238-b61b-47a4-92d6-74435c3b556d
-- title:
--   Examples: unary mem of length le
-- statement:
--   Over a unary constructor a word is determined by its length, so a tree containing a
--   position contains every shorter one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L46-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean#L46-L51

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints

theorem DeciSigma1.Examples.unary_mem_of_length_le (t : PrefixSet 1) {u v : List (Fin 1)}
    (h : u.length ≤ v.length) (hv : v ∈ t.carrier) : u ∈ t.carrier := by sorry
