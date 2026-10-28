-- Prove2me | Theorems.Thm_Cslib_PolynomiallyBounded_mul
-- name    : Cslib.PolynomiallyBounded.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:59:46.412877+00:00
-- url     : https://prove2.me/theorems/551934d6-31ef-4f0c-992c-6ef52f675fb6
-- title:
--   Polynomial growth is closed under multiplication
-- statement:
--   If $f,g:\mathbb N\to\mathbb N$ are polynomially bounded, then $n\mapsto f(n)g(n)$ is polynomially bounded. This supports constant factors and products in resource estimates; it makes no assertion about computational cost by itself.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/36f94d8deb5ada759c302a6df86d55e68981c7d1/Complexity/Foundations/Data/Nat/PolynomialBound/Closure.lean#L102-L110

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

theorem Cslib.PolynomiallyBounded.mul (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  sorry
