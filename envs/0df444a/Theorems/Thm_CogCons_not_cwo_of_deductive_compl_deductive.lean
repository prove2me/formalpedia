-- Prove2me | Theorems.Thm_CogCons_not_cwo_of_deductive_compl_deductive
-- name    : CogCons.not_cwo_of_deductive_compl_deductive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T17:41:47.751671+00:00
-- url     : https://prove2.me/theorems/ac287985-5c2c-40e8-b365-807af6d45d2b
-- title:
--   Theorem 3.5: a set and its complement cannot both be deductive
-- statement:
--   If a set $A$ of mental representations and its complement $C \setminus A$ are both deductive systems, then $A \notin \tau$.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, Theorem 3.5 (p. 7)

import Mathlib
import Definitions.Def_CogCons_consequence_space

open CogCons.CognitiveConsequenceSpace

namespace CogCons

theorem not_cwo_of_deductive_compl_deductive {C : Type*} (S : CognitiveConsequenceSpace C)
    (A : Set C) (hA : S.IsDeductive A) (hAc : S.IsDeductive Aᶜ) :
    ¬ S.IsCWO A := by sorry

end CogCons
