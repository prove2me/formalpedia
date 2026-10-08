-- Prove2me | Theorems.Thm_ContactLinearAlgebra_reeb_exists_unique
-- name    : ContactLinearAlgebra.reeb_exists_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T14:26:20.722231+00:00
-- url     : https://prove2.me/theorems/20c59d8b-bb1d-4ca3-8ac2-9c8877a86631
-- title:
--   Existence and uniqueness of the Reeb vector in a finite-dimensional contact vector space
-- statement:
--   Let V be a finite-dimensional real vector space, a a nonzero linear functional, and b an alternating bilinear form. Assume the restriction of b to ker a is non-degenerate: if u lies in ker a and b(u,v)=0 for every v in ker a, then u=0. There is a unique vector R satisfying
--
--   $$a(R)=1, \qquad b(R,v)=0 \quad(v\in V).$$
--
--   This is the pointwise linear-algebra form of the Reeb-vector theorem, usable independently of any manifold or regular-level representation.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/pdf/math/0307242, Remark 2.3 (p. 4) and Definition 2.5 with following paragraph (p. 6). Abstract pointwise linear-algebra formulation using non-degeneracy on the contact hyperplane; no manifold hypotheses are required.

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

theorem ContactLinearAlgebra.reeb_exists_unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hb : ∀ v, b v v = 0) (ha : ∃ v, a v ≠ 0)
    (hn : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0) :
    ∃! R : V, a R = 1 ∧ ∀ v, b R v = 0 := by sorry
