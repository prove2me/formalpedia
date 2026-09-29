-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar
-- name    : AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e3c8f0af-facf-53b9-8ec3-b6ac4d4f23a6
-- title:
--   Archimedean twisted descent for ℂ/ℝ at a real scalar
-- statement:
--   Fix Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, each for the Borel $\sigma$-algebra of the group, a function $\varphi:\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ which is of the form $g\mapsto \Phi((g_{ij}))$ for some $\Phi:(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{C})\to\mathbb{C}$ that is $C^\infty$ over $\mathbb{R}$ and which has compact support, and a unit $d\in\mathbb{R}^\times$. The assertion is that there exists $\psi:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$, again of the form $g\mapsto\Psi((g_{ij}))$ with $\Psi$ of class $C^\infty$ over $\mathbb{R}$ and with compact support, together with a neighbourhood $U$ of $1$ in $\mathrm{GL}_2(\mathbb{R})$, with the following property. For every $t\in U$ such that $t=1$ or $\operatorname{tr}(t)^2-4\det(t)$ is a unit, for every Haar measure $\tau$ on the centraliser of $\{t\}$ in $\mathrm{GL}_2(\mathbb{R})$ and every Haar measure $\tau'$ on the $\sigma$-twisted centraliser $\{x: x\,\delta\,\sigma(x)^{-1}=\delta\}$ of $\delta=\iota(t\cdot d\,\mathrm{I})$, where $\iota$ is the base-change map $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ induced by $\mathrm{includeRight}$ and $\sigma$ acts entrywise through complex conjugation on the tensor factor, such that $\tau$ and $\tau'$ are coupled through $y=1$, i.e. the pushforward of $\tau'$ along the inclusion of the twisted centraliser coincides with the pushforward of $\tau$ along $\iota$, and for every $I'\in\mathbb{C}$: the number $I'$ is a twisted orbital value at $\delta$ of $\varphi$ transported along the identification $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$ (that is, there is a non-negative measurable $w$ of compact support with $\int w(u x)\,\mathrm{d}\tau'(u)=1$ whenever the integrand $\varphi$-value at $x^{-1}\delta\,\sigma(x)$ is non-zero, and $I'=\int \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,\mathrm{d}\mu_L$) if and only if $I'$ is an orbital value of $\psi$ at $t$ in the same sense, with $\mu_A$, $\tau$ and $x^{-1}tx$ in place of $\mu_L$, $\tau'$ and $x^{-1}\delta\,\sigma(x)$.
--
--   This is the archimedean case of twisted descent (Harish-Chandra descent in the twisted setting, as in Langlands' treatment of base change for $\mathrm{GL}(2)$): a smooth compactly supported test function on $\mathrm{GL}_2(\mathbb{C})$ is replaced by one on $\mathrm{GL}_2(\mathbb{R})$ matching twisted orbital integrals at $t\cdot d\,\mathrm{I}$ with ordinary orbital integrals at $t$, for $t$ near $1$. It feeds the comparison of orbital data at scalar elements used further on in the base-change input to the trace-formula comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ) :
    ∃ ψ : GL (Fin 2) ℝ → ℂ,
      ((∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ) ∧
      ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, (t = 1 ∨ IsRegularSemisimple t) →
        ∀ (τ : @Measure (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ t))
          (τ' : @Measure
            (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ t) τ →
          @Measure.IsHaarMeasure _ _ _
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe t (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))
            1 τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' ↔
            IsOrbitalIntegralOn ℝ μA t τ ψ I' := by sorry
