-- Prove2me | Theorems.Thm_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
-- name    : AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/37fd23f9-2d1a-5488-8ece-ac0e8908fbc8
-- title:
--   Smoothness and compact support of an archimedean twisted integral
-- statement:
--   Fix a measure $\mu_L$ on $GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ for the Borel $\sigma$-algebra `glBorelOf (ℂ ⊗[ℝ] ℝ)` of the topology on $GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, and assume $\mu_L$ is a Haar measure. Let $\varphi : GL_2(\mathbb{C}) \to \mathbb{C}$ be such that, first, there is a map $\Phi$ on all of $\mathbb{C}^{2\times 2}$ which is $C^\infty$ over $\mathbb{R}$ and satisfies $\varphi(g) = \Phi\bigl((g_{ij})\bigr)$ for every $g$, and, second, $\varphi$ has compact support. Let $d \in \mathbb{R}^\times$, and let $\alpha : GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}) \to \mathbb{R}$ be continuous with compact support. Let $\psi : GL_2(\mathbb{R}) \to \mathbb{C}$ satisfy, for all $s$,
--   $$\psi(s) = \int \alpha(x)\,\varphi\Bigl(\bigl(x^{-1}\,\iota(s \cdot d I_2)\,\sigma(x)\bigr)^{\mathbb{C}}\Bigr)\,d\mu_L(x),$$
--   where $\iota =$ `toTensorGL ℝ ℂ ℝ` is induced by $a \mapsto 1 \otimes a$, $d I_2 =$ `Matrix.GeneralLinearGroup.scalar (Fin 2) d`, $\sigma =$ `sigmaGL ℝ ℂ ℝ Complex.conjAe` is induced entrywise by complex conjugation on the left tensor factor, and $(\,\cdot\,)^{\mathbb{C}}$ denotes transport along the entrywise isomorphism $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R} \cong \mathbb{C}$ given by `Algebra.TensorProduct.rid`. The conclusion is that $\psi$ is again of the same shape: there is a map $\Psi$ on all of $\mathbb{R}^{2\times 2}$, $C^\infty$ over $\mathbb{R}$, with $\psi(g) = \Psi\bigl((g_{ij})\bigr)$ for all $g$, and $\psi$ has compact support.
--
--   This is the archimedean regularity step in the twisted descent from $GL_2(\mathbb{C})$ to $GL_2(\mathbb{R})$: integrating a compactly supported smooth test function over the twisted conjugation orbit against a compactly supported continuous weight again produces a compactly supported function that is smooth in the matrix entries. It is used by [`AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar`](thm.html#AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar), where the descended function must be a legitimate test function at the archimedean place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α)
    (ψ : GL (Fin 2) ℝ → ℂ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∂μL) :
    (∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ := by sorry
