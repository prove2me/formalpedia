-- Prove2me | Theorems.Thm_Eden_coeff_vectorFieldPolynomial_first
-- name    : Eden.coeff_vectorFieldPolynomial_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:30.676881+00:00
-- url     : https://prove2.me/theorems/28ab9d80-5e73-52bb-98ae-c109e284272b
-- title:
--   Eden: coeff vector Field Polynomial first
-- statement:
--   The Eden construction uses the coeff vector Field Polynomial first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L74-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L74-L85

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.coeff_vectorFieldPolynomial_first (c : ℝ) :
    (vectorFieldPolynomial c 0).coeff (Finsupp.single 0 5) = -1 := by sorry
