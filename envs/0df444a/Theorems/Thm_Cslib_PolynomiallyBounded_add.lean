-- Prove2me | Theorems.Thm_Cslib_PolynomiallyBounded_add
-- name    : Cslib.PolynomiallyBounded.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T00:58:56.944225+00:00
-- url     : https://prove2.me/theorems/8dd440ac-618f-41dc-8dab-f3ae966771a9
-- title:
--   Polynomial growth is closed under addition
-- statement:
--   If $f,g:\mathbb N\to\mathbb N$ are polynomially bounded, then $n\mapsto f(n)+g(n)$ is polynomially bounded. In the counting-matroid implementation bridge this combines the input-size allowance with the already-proved bound on source charges.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/36f94d8deb5ada759c302a6df86d55e68981c7d1/Complexity/Foundations/Data/Nat/PolynomialBound/Closure.lean#L91-L100

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

theorem Cslib.PolynomiallyBounded.add (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  sorry
