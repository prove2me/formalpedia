-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe
-- name    : AutomorphicForm.GL2Real.exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/7dc446bc-05e3-5591-a67d-510c63f6a332
-- title:
--   Normal forms and norm fibres in GL₂(ℝ)
-- statement:
--   Throughout, $\sigma$ denotes the involution of $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ induced entrywise by $\mathrm{Complex.conjAe}\otimes\mathrm{id}$, an element $\gamma\in\mathrm{GL}_2(\mathbb{R})$ is viewed in $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ through the right inclusion, and $\mathrm{IsNormConjugator}$ with conjugator $1$ says that this image equals the norm string $\prod_{i<[\mathbb{C}:\mathbb{R}]}\sigma^{i}(\delta_1)=\delta_1\,\sigma(\delta_1)$; $\mathrm{upperTriangular}\,a_1\,a_2\,0$ is $\mathrm{diag}(a_1,a_2)$, $\mathrm{ellipticElt}\,r\,\theta$ is $\begin{pmatrix} r\cos\theta & r\sin\theta\\ -r\sin\theta & r\cos\theta\end{pmatrix}$, regular semisimplicity of $\gamma$ means $\operatorname{tr}(\gamma)^2-4\det(\gamma)$ is a unit, and the twisted centraliser of $\delta_1$ is $\{t : t\,\delta_1\,\sigma(t)^{-1}=\delta_1\}$. Four assertions are made. (1) Every regular semisimple $\gamma\in\mathrm{GL}_2(\mathbb{R})$ satisfies $x^{-1}\gamma x=\mathrm{diag}(a_1,a_2)$ for some $x$ and some $a_1\neq a_2$ with $a_1a_2\neq0$, or $x^{-1}\gamma x=\mathrm{ellipticElt}\,r\,\theta$ with $r>0$ and $0<\theta<\pi$. (2) If $a_1a_2\neq0$, $a_1\neq a_2$ and $\delta_1\sigma(\delta_1)$ is the image of $\mathrm{diag}(a_1,a_2)$, then $a_1>0$ and $a_2>0$, and there exist $t,\delta_0$ with $\delta_0$ corresponding under $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$ to $\mathrm{diag}(\sqrt{a_1},\sqrt{a_2})$, with $\delta_1=t^{-1}\delta_0\,\sigma(t)$ and with $t$ commuting with every element of the twisted centraliser of $\delta_1$. (3) If $r>0$, $\sin\theta\neq0$ and $\delta_1\sigma(\delta_1)$ is the image of $\mathrm{ellipticElt}\,r\,\theta$, the same conclusion holds with $\delta_0$ corresponding to $\sqrt{r}\begin{pmatrix}\cos(\theta/2)&\sin(\theta/2)\\-\sin(\theta/2)&\cos(\theta/2)\end{pmatrix}$. (4) If $\gamma$ is regular semisimple and no $\delta$ satisfies $\mathrm{IsNormOf}$ for $\gamma$ (that is, no $\delta,y$ give $\gamma=y^{-1}\delta\sigma(\delta)y$), then $x^{-1}\gamma x=\mathrm{diag}(a_1,a_2)$ for some $x$ and some $a_1\neq a_2$ with $a_1a_2\neq0$ and $a_1<0$ or $a_2<0$.
--
--   This is the archimedean part of the norm correspondence for base change from $\mathbb{R}$ to $\mathbb{C}$ for $\mathrm{GL}(2)$: normal forms for regular semisimple real conjugacy classes (split or elliptic), an explicit description of the fibre of the twisted norm over such a class together with a twisted-centraliser-commuting conjugator, and the observation that classes failing to be norms are exactly split ones with a negative eigenvalue. It is used in the construction of a smooth compactly supported test function whose twisted orbital integrals for complex conjugation determine the relevant comparison of orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.GL2Real.exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe :
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
      ∃ x : GL (Fin 2) ℝ,
        (∃ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) ∨
        (∃ (r θ : ℝ) (hr : 0 < r), 0 < θ ∧ θ < Real.pi ∧ x⁻¹ * γ * x = ellipticElt r θ hr)) ∧
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (upperTriangular a₁ a₂ 0 h) δ₁ 1 →
          (0 < a₁ ∧ 0 < a₂) ∧
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (ellipticElt r θ hr) δ₁ 1 →
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
                ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
      ∃ (x : GL (Fin 2) ℝ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0),
        a₁ ≠ a₂ ∧ (a₁ < 0 ∨ a₂ < 0) ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) := by sorry
