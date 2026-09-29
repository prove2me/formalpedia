-- Prove2me | Theorems.Thm_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
-- name    : AutomorphicForm.pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/76487bd7-bf0b-54db-9370-5d0e62cc3ca8
-- title:
--   Coupled pair at a scalar norm: c>0 and transfer to √c 1
-- statement:
--   Work with the quadratic extension $\mathbb{C}/\mathbb{R}$, the base ring $A=\mathbb{R}$ and the twist $\sigma=$ `Complex.conjAe`, so that $\sigma$ acts on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ through the map `sigmaGL`. Let $\mu$ be a measure on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, for the Borel structure `glBorelOf`, which is invariant under all left translations $z\mapsto gz$. Let $c\in\mathbb{R}^{\times}$ and let $\delta,y\in\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ satisfy `IsNormConjugator`, i.e. the image of the scalar matrix $c\cdot 1$ under `toTensorGL` equals $y^{-1}\,\delta\,\sigma(\delta)\,y$ (the norm string being the product over $i<\dim_{\mathbb{R}}\mathbb{C}$ of the iterates $\sigma^{i}(\delta)$). Let $\tau$ be a Haar measure on the centraliser of $c\cdot 1$ in $\mathrm{GL}_2(\mathbb{R})$ and $\tau'$ a Haar measure on the twisted centraliser $\{t: t\,\delta\,\sigma(t)^{-1}=\delta\}$ of $\delta$, both with their Borel structures, and assume the pair is `Coupled`: the pushforward of $\tau'$ along $t\mapsto y^{-1}ty$ coincides with the pushforward of $\tau$ along `toTensorGL`. The conclusion is that $c>0$ and that there exist $d\in\mathbb{R}^{\times}$ with $d\cdot d=c$ and a Haar measure $\tau_1$ on the twisted centraliser of $\delta_1:=$ `toTensorGL` $(d\cdot 1)$ such that $\tau$ and $\tau_1$ are `Coupled` relative to $c\cdot 1$, $\delta_1$ and the conjugator $y=1$, and such that for every $\varphi:\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})\to\mathbb{C}$ and every $I\in\mathbb{C}$, $I$ is a twisted orbital integral of $\varphi$ at $\delta$ with respect to $\mu$ and $\tau'$ if and only if it is one at $\delta_1$ with respect to $\mu$ and $\tau_1$; here being such an integral means that there is a non-negative measurable compactly supported weight $w$ with $\int w(tx)\,d\tau=1$ for all $x$ with $\varphi(x^{-1}\,\delta\,\sigma(x))\neq 0$ (the integral over the relevant twisted centraliser) and $I=\int \varphi(x^{-1}\,\delta\,\sigma(x))\,w(x)\,d\mu$.
--
--   This is the archimedean normalisation step in the comparison of twisted orbital integrals for $\mathbb{C}/\mathbb{R}$ at a central element: the existence of a coupled pair of Haar measures above a real scalar $c$ forces $c$ to be positive and allows the twisted conjugacy datum $(\delta,y)$ to be replaced by the scalar representative $d\cdot 1$ with $d^{2}=c$, coupled through the identity conjugator. It is used in the archimedean matching and transfer statements for scalar elements, including the identification of a twisted orbital integral with a sign times an ordinary orbital integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : ∀ g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      @Measure.map _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) (fun z => g * z) μ = μ)
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hC : Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ') :
    0 < (c : ℝ) ∧
    ∃ d : ℝˣ, (d : ℝ) * d = c ∧
      ∃ τ₁ : @Measure
          (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))),
        @Measure.IsHaarMeasure _ _ _
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ₁ ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (I : ℂ),
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ' φ I ↔
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ
              (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ₁ φ I := by sorry
