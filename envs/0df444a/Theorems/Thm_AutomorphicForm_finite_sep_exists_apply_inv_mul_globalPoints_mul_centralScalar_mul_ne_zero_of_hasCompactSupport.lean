-- Prove2me | Theorems.Thm_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
-- name    : AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a5795c1d-62e0-5a3e-98cf-148452e567b9
-- title:
--   Finiteness of central and elliptic terms for GL₂
-- statement:
--   Let $K$ be a number field, let $E$ be a type with a distinguished element $0$, and let $f\colon GL_2(\mathbb{A}_K)\to E$ be a function on the group of invertible $2\times 2$ matrices over the adele ring of $K$ (here [`AutomorphicForm.AdelicGL2 (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L12)) whose support has compact closure. Let $R\subseteq GL_2(K)$ be a set of matrices contained in the union of the central cell, consisting of those $\gamma$ whose underlying matrix equals $c\cdot 1$ for some $c\in K$, and the elliptic cell, consisting of those $\gamma$ whose characteristic polynomial has no root in $K$. Assume that every $\gamma$ in this union admits exactly one $\gamma_0\in R$ for which $\gamma = \mathrm{scalar}(a)\cdot(h^{-1}\gamma_0 h)$ for some $h\in GL_2(K)$ and some $a\in K^\times$, the scalar being the image of $a$ in the centre of $GL_2(K)$. Then the set of those $\gamma_0\in R$ for which there exist $x\in GL_2(\mathbb{A}_K)$ and an idele $z\in\mathbb{A}_K^\times$ with
--   $$f\bigl(x^{-1}\,\iota(\gamma_0)\,(\mathrm{scalar}(z)\,x)\bigr)\neq 0,$$
--   where $\iota$ is the entrywise map $GL_2(K)\to GL_2(\mathbb{A}_K)$ induced by $K\to\mathbb{A}_K$ and $\mathrm{scalar}(z)$ is the central matrix attached to $z$, is finite.
--
--   This is the finiteness, for a fixed compactly supported test function, of the set of central and elliptic terms occurring on the geometric side of the trace formula for $GL_2$ over a number field: each term is indexed by a class $\gamma_0\in R$ and involves an integral of $x\mapsto f(x^{-1}\gamma_0 z x)$ over the ideles $z$ and over $x$. It is used to know that the two class sums compared in the elliptic term of cyclic base change for $GL_2$ are finite sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.finite_sep_exists_apply_inv_mul_globalPoints_mul_centralScalar_mul_ne_zero_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K]
    {E : Type*} [Zero E]
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → E) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) K))
    (hRsub : R ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ R ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ),
        γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h)) :
    {γ₀ ∈ R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ≠ 0}.Finite := by sorry
