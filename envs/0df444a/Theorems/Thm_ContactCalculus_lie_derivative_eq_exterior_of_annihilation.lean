-- Prove2me | Theorems.Thm_ContactCalculus_lie_derivative_eq_exterior_of_annihilation
-- name    : ContactCalculus.lie_derivative_eq_exterior_of_annihilation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T18:45:13.345982+00:00
-- url     : https://prove2.me/theorems/f6fd4683-9580-48b2-a6a5-39ab4a46b0d1
-- title:
--   Cartan identity for a one-form annihilating a vector field
-- statement:
--   Let $V$ be a real normed vector space, let $\eta:V\to V^*$ be a differentiable one-form, and let $X:V\to V$ be a differentiable vector field. Suppose $\eta_y(X(y))=0$ at every point. For every $y,v\in V$,
--
--   $$D\eta(y)[X(y)](v)+\eta_y(DX(y)[v])=D\eta(y)[X(y)](v)-D\eta(y)[v](X(y)).$$
--
--   Equivalently, $\mathcal L_X\eta=i_Xd\eta$. Here $V^*$ is the continuous real dual. This is the annihilation case of Cartan's formula used in the contact Moser equation. The annihilation hypothesis holds on the whole ambient space, so its derivative in every direction is zero.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15: Cartan formula and the choice X_t in ker α_t before equation (2.1). Ambient normed-space generalization under global annihilation; only first differentiability is used.

import Mathlib.Analysis.Calculus.FDeriv.Basic

theorem ContactCalculus.lie_derivative_eq_exterior_of_annihilation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : V → (V →L[ℝ] ℝ)) (X : V → V)
    (hη : Differentiable ℝ η) (hX : Differentiable ℝ X)
    (hz : ∀ y, η y (X y) = 0) (y v : V) :
    fderiv ℝ η y (X y) v + η y (fderiv ℝ X y v) =
      fderiv ℝ η y (X y) v - fderiv ℝ η y v (X y) := by sorry
