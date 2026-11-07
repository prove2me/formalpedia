-- Prove2me | Theorems.Thm_CubicProductLB_lemma_12
-- name    : CubicProductLB.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:40.385251+00:00
-- url     : https://prove2.me/theorems/b22c085a-d616-42e3-b39e-288ac30bacab
-- title:
--   Lemma 12 — cubic units depend on boundedly many affine observations
-- statement:
--   There is an absolute constant $R$ such that every cubic unit on every $X_n$ depends on at most $R$ affine observations. Here a **cubic unit** is a function of multilinear degree at most three on $X_n$ that is nowhere zero there, which over $\mathbb F_3$ means that it takes values in $\{1, -1\}$ on $X_n$.
--
--   The constant does not depend on $n$ nor on the unit. A cubic unit may have large coordinate support, but all of its dependence is compressed into a bounded-dimensional affine image over $\mathbb F_3$. This is the structural heart of the lower bound.
--
--   Differences from the source:
--   - encoding: a cubic unit, i.e. a polynomial → any function f with multilinear degree at most 3 on X_n and no zero on X_n; reason: the condition and the conclusion concern only the values on X_n; same instances
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 12, p.19

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_HasMultilinearDegLE
import Definitions.Def_CubicProductLB_DependsOnAtMost

namespace CubicProductLB

/-- Lemma 12 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 12, p.19). There is an absolute constant `R` such that every cubic unit on
every `X_n` depends on at most `R` affine observations.

**Formalization Note** `R` comes before `n` and `f` ("independent of n", Remark 13, p.26). A cubic unit
is a function of multilinear degree at most three on `X_n` that vanishes nowhere there (Eq. (3), p.4). -/
theorem lemma_12 :
    ∃ R : ℕ, ∀ (n : ℕ) (f : (Fin n → ZMod 3) → ZMod 3),
      HasMultilinearDegLE 3 f → (∀ x ∈ signCube n, f x ≠ 0) → DependsOnAtMost R f := by sorry

end CubicProductLB
