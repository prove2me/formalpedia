-- Prove2me | Theorems.Thm_Cslib_PolynomiallyBounded_pow
-- name    : Cslib.PolynomiallyBounded.pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:01:29.943198+00:00
-- url     : https://prove2.me/theorems/53c890de-b9a5-44b6-933d-9991c2605300
-- title:
--   Fixed powers preserve polynomial growth
-- statement:
--   For a polynomially bounded function $f:\mathbb N\to\mathbb N$ and a fixed natural exponent $d$, the function $n\mapsto f(n)^d$ is polynomially bounded. The exponent is fixed uniformly across inputs.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/36f94d8deb5ada759c302a6df86d55e68981c7d1/Complexity/Foundations/Data/Nat/PolynomialBound/Closure.lean#L112-L119

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.FunProp
import Definitions.Def_CSLib_PolynomialGrowth
import Theorems.Thm_Cslib_polynomiallyBounded_iff_le

open Filter Cslib
variable {f g : ℕ → ℕ}

theorem Cslib.PolynomiallyBounded.pow (hf : PolynomiallyBounded f) (d : ℕ) :
    PolynomiallyBounded (fun n => f n ^ d) := by
  sorry
