-- Prove2me | Theorems.Thm_ContactLinearAlgebra_moser_equation_exists_unique
-- name    : ContactLinearAlgebra.moser_equation_exists_unique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:12:26.948488+00:00
-- url     : https://prove2.me/theorems/08368ca9-6564-4190-befb-62c6a4325fc9
-- title:
--   Unique solution of a linear Moser equation on a hyperplane
-- statement:
--   Let $V$ be a finite-dimensional real vector space, $a:V\to\mathbb R$ a nonzero linear functional, and $b:V\times V\to\mathbb R$ a bilinear form whose restriction to $\ker a$ is left non-degenerate. Thus, if $a(u)=0$ and $b(u,v)=0$ for every $v\in\ker a$, then $u=0$. For every linear functional $\beta$ there is a unique $X\in\ker a$ such that some $\mu\in\mathbb R$ satisfies
--
--   $$\beta(v)+b(X,v)=\mu a(v)\qquad(v\in V).$$
--
--   This generalizes the pointwise linear algebra in the Moser argument: alternation of $b$ is unnecessary for existence and uniqueness. In the contact case $a=\alpha_y$ and $b=d\alpha_y$ on the tangent space. If $R$ is the Reeb vector, evaluation at $R$ gives $\mu=\beta(R)$.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, p. 15, equations (2.1)–(2.2). Generalization of the pointwise linear-algebra step to arbitrary bilinear forms non-degenerate on ker a.

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

namespace ContactLinearAlgebra

theorem moser_equation_exists_unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (ha : ∃ v, a v ≠ 0)
    (hn : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0)
    (β : V →ₗ[ℝ] ℝ) :
    ∃! X : V, a X = 0 ∧ ∃ μ : ℝ, ∀ v, β v + b X v = μ * a v := by sorry

end ContactLinearAlgebra
