-- Prove2me | Theorems.Thm_Eden_eval_vectorFieldPolynomial
-- name    : Eden.eval_vectorFieldPolynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:28:47.490801+00:00
-- url     : https://prove2.me/theorems/c7903211-ed76-4a62-9651-ed61d51293b3
-- title:
--   Eden: eval vector Field Polynomial
-- statement:
--   The Eden construction uses the eval vector Field Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L37-L41
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L37-L41

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.eval_vectorFieldPolynomial (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    eval (fun j => p j) (vectorFieldPolynomial c i) = vectorField c p i := by sorry
