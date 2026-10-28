-- Prove2me | Theorems.Thm_Cslib_PolynomiallyBounded_comp
-- name    : Cslib.PolynomiallyBounded.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:02:16.85477+00:00
-- url     : https://prove2.me/theorems/9cb2d1eb-8e3d-4889-997e-0c2898207057
-- title:
--   Polynomial growth is closed under composition
-- statement:
--   If $f,g:\mathbb N\to\mathbb N$ are polynomially bounded, then $n\mapsto f(g(n))$ is polynomially bounded. The counting-matroid bridge uses this to compose a proposed simulator's polynomial overhead with the imported estimator's polynomial resource bound. Establishing that the simulator actually realizes that overhead remains a separate implementation obligation.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/36f94d8deb5ada759c302a6df86d55e68981c7d1/Complexity/Foundations/Data/Nat/PolynomialBound/Closure.lean#L121-L136

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

theorem Cslib.PolynomiallyBounded.comp (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  sorry
