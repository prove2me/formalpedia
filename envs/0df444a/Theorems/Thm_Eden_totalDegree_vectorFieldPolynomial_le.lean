-- Prove2me | Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_le
-- name    : Eden.totalDegree_vectorFieldPolynomial_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:01:07.169683+00:00
-- url     : https://prove2.me/theorems/888f1256-b894-4063-b010-adab854c36a4
-- title:
--   Eden: total Degree vector Field Polynomial le
-- statement:
--   The Eden construction uses the total Degree vector Field Polynomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L58-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L58-L72

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.totalDegree_vectorFieldPolynomial_le (c : ℝ) (i : Fin 5) :
    (vectorFieldPolynomial c i).totalDegree ≤ 5 := by sorry
