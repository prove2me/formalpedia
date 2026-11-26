-- Prove2me | Theorems.Thm_Eden_totalDegree_ratePolynomial_le
-- name    : Eden.totalDegree_ratePolynomial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:15.687475+00:00
-- url     : https://prove2.me/theorems/1e45137e-e61e-4691-98c5-9881e176dc01
-- title:
--   Eden: total Degree rate Polynomial le
-- statement:
--   The Eden construction uses the total Degree rate Polynomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L47-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L47-L56

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.totalDegree_ratePolynomial_le (i j : Fin 5) :
    (ratePolynomial i j).totalDegree ≤ 4 := by sorry
