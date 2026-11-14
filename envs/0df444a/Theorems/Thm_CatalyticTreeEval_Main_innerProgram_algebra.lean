-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_innerProgram_algebra
-- name    : CatalyticTreeEval.Main.innerProgram_algebra
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T01:45:37.986099+00:00
-- url     : https://prove2.me/theorems/d5a0df93-ccf1-4259-abf3-690eea65b234
-- title:
--   Four-query masked scalar program: algebra, restoration and inverse pairs
-- statement:
--   For arbitrary residue-vector families, hidden labels and initial registers, the literal swap-and-query program returns the sum of the two masked inner products. It restores all three registers, pairs each child update with its exact inverse, and uses exactly four positional oracle queries. Matching-vector and decoder hypotheses are unnecessary for this algebraic statement; machine realization is a separate component of Lemma4.5.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section3.1 and Lemma4.5. Native sequencing uses the standard halting-redirection construction.

import Definitions.Def_CatalyticTreeEval_Main_RegisterProgram
open CatalyticTreeEval.Main
set_option autoImplicit false

theorem CatalyticTreeEval.Main.innerProgram_algebra {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    (innerProgram U V x R).1 = (R 0 ⬝ᵥ V (x 0)) + (R 1 ⬝ᵥ V (x 1)) ∧
    execute U V x R (innerProgram U V x R).2 = R ∧
    InversePairs (innerProgram U V x R).2 ∧
    ((innerProgram U V x R).2.filter fun op =>
      match op with | .query _ _ _ => true | _ => false).length = 4 := by sorry
