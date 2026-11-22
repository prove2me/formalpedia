-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_drop_eq_take_append_site
-- name    : DeciSigma1.Holes.Fresh.drop_eq_take_append_site
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:17.793805+00:00
-- url     : https://prove2.me/theorems/d4acb326-4c78-42a7-9740-3255709b8da0
-- title:
--   Fresh: drop eq take append site
-- statement:
--   The Fresh construction uses the drop eq take append site property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L153-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/DeletionCoordinates.lean#L153-L157

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} {δ : ℕ}

theorem DeciSigma1.Holes.Fresh.drop_eq_take_append_site {x : List α} {F : List α} {p d c : ℕ} (hpc : p + d = c)
    (hF : (x.drop c).take δ = F) :
    x.drop p = (x.drop p).take d ++ (F ++ x.drop (c + δ)) := by sorry
