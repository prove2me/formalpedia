-- Prove2me | Theorems.Thm_Eden_vectorFieldPolynomial_degree
-- name    : Eden.vectorFieldPolynomial_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:41.432824+00:00
-- url     : https://prove2.me/theorems/c6729954-95c7-58a4-ba62-30b152ae9d6c
-- title:
--   Eden: vector Field Polynomial degree
-- statement:
--   The degree of the polynomial vector field is exactly five, for every real value
--   of its parameter.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L97-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean#L97-L103

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial

theorem Eden.vectorFieldPolynomial_degree (c : ℝ) :
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 := by sorry
