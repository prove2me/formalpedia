-- Prove2me | Theorems.Thm_Evaluate_evaluate_terminal
-- name    : Evaluate.evaluate_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:07.170865+00:00
-- url     : https://prove2.me/theorems/0936e439-da00-4892-91fe-365895154b53
-- title:
--   Evaluate: evaluate terminal
-- statement:
--   The Evaluate construction uses the evaluate terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Evaluate.lean#L24-L26
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Evaluate.lean#L24-L26

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Evaluate
set_option autoImplicit true
open Evaluate

theorem Evaluate.evaluate_terminal {O : OBdd n m} : O.1.root = .terminal b → evaluate O = Function.const _ b := by sorry
