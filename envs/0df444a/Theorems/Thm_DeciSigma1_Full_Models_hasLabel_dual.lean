-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_hasLabel_dual
-- name    : DeciSigma1.Full.Models.hasLabel_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:18.68809+00:00
-- url     : https://prove2.me/theorems/80aa3c93-96f1-4a5d-af3c-2df65ae1d793
-- title:
--   Models: has Label dual
-- statement:
--   The Models construction uses the has Label dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L85-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L85-L93

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Models.hasLabel_dual (t : Semantics.Tree n) (w : List (Fin n)) :
    Semantics.Tree.HasLabel (Tree.dual t) w Sym.bot ↔ Semantics.Tree.HasLabel t w Sym.top := by sorry
