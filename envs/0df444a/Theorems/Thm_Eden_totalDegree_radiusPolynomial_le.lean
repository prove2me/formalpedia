-- Prove2me | Theorems.Thm_Eden_totalDegree_radiusPolynomial_le
-- name    : Eden.totalDegree_radiusPolynomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:09.875786+00:00
-- url     : https://prove2.me/theorems/301e23b7-9e06-4558-8eb4-6fc83cc9b00e
-- title:
--   Eden: total Degree radius Polynomial le
-- statement:
--   The Eden construction uses the total Degree radius Polynomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L43-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L43-L45

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.totalDegree_radiusPolynomial_le (i j : Fin 5) :
    (radiusPolynomial i j).totalDegree ≤ 2 := by sorry
