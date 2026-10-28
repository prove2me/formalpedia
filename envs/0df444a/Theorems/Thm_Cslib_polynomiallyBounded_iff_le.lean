-- Prove2me | Theorems.Thm_Cslib_polynomiallyBounded_iff_le
-- name    : Cslib.polynomiallyBounded_iff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:58:17.198536+00:00
-- url     : https://prove2.me/theorems/2f8a3655-aa9e-4a03-9135-7aa4fe6c7c82
-- title:
--   Polynomial growth admits a uniform monomial bound
-- statement:
--   For every $f:\mathbb N\to\mathbb N$, eventual domination by a fixed power is equivalent to the existence of natural constants $c,d$ such that $f(n)\le c(n+1)^d$ for every natural $n$. The coefficient absorbs the finite initial segment. This converts an asymptotic growth certificate into the uniform bound required by the counting-matroid machine specification.
-- source:
--   https://github.com/leanprover/cslib/blob/6ff325e870ed89f86be10515f0e7297fa5a32845/Cslib/Foundations/Data/Nat/PolynomialBound.lean#L48-L68

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.FunProp
import Definitions.Def_CSLib_PolynomialGrowth

open Filter Cslib
variable {f g : ℕ → ℕ}

theorem Cslib.polynomiallyBounded_iff_le {f : ℕ → ℕ} :
    PolynomiallyBounded f ↔ ∃ c d : ℕ, ∀ n, f n ≤ c * (n + 1) ^ d := by
  sorry
