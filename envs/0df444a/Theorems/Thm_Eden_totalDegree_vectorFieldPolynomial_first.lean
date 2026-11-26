-- Prove2me | Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_first
-- name    : Eden.totalDegree_vectorFieldPolynomial_first
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:04:29.902531+00:00
-- url     : https://prove2.me/theorems/9395ee8a-4d51-58c1-bac2-c399c5d8cd71
-- title:
--   Eden: total Degree vector Field Polynomial first
-- statement:
--   The Eden construction uses the total Degree vector Field Polynomial first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L87-L93
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L87-L93

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.totalDegree_vectorFieldPolynomial_first (c : ℝ) :
    (vectorFieldPolynomial c 0).totalDegree = 5 := by sorry
