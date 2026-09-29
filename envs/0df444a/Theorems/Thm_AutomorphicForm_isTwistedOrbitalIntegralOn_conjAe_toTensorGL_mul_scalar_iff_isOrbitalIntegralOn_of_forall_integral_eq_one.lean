-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one
-- name    : AutomorphicForm.isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/f75c862c-0718-52ed-813a-00a9f567b9d5
-- title:
--   Archimedean twisted descent for GL₂(ℂ)/GL₂(ℝ)
-- statement:
--   Fix Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb R}\mathbb{R})$, both for the Borel $\sigma$-algebras `glBorelOf`, and a function $\varphi:\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ which is compactly supported and is the restriction of a real-$C^\infty$ function of the matrix entries. Let $d\in\mathbb{R}^\times$, assume the monoid homomorphism $\iota=$ `toTensorGL ℝ ℂ ℝ` (induced by $a\mapsto 1\otimes a$) is a closed embedding, and let $t\in\mathrm{GL}_2(\mathbb{R})$ be either $1$ or regular semisimple in the sense that $\operatorname{tr}(t)^2-4\det(t)$ is a unit. Put $\delta=\iota(t\cdot d\,\mathrm{Id})$ and let $\sigma$ be the automorphism of $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb R}\mathbb{R})$ induced by complex conjugation on the left factor. Assume the twisted centralizer $\{x : x\delta\sigma(x)^{-1}=\delta\}$ is exactly $\iota$ of the centralizer of $t$. Let $\alpha\ge 0$ be continuous and compactly supported on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb R}\mathbb{R})$ with $\int\alpha(\iota(m)x)\,d\mu_A(m)=1$ for every $x$ at which $\varphi(x^{-1}\delta\sigma(x))\ne 0$ (entries transported to $\mathrm{GL}_2(\mathbb{C})$ by `Algebra.TensorProduct.rid`), and let $\psi:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ be continuous with $\psi(s)=\int\alpha(x)\,\varphi\bigl(x^{-1}\iota(s\cdot d\,\mathrm{Id})\sigma(x)\bigr)\,d\mu_L(x)$. Let $\tau$, $\tau'$ be Haar measures on the centralizer of $t$ and on the twisted centralizer of $\delta$, coupled in the sense that the image of $\tau'$ under conjugation by $y=1$ coincides with the image of $\tau$ under $\iota$. Then, for $I'\in\mathbb{C}$: there is a nonnegative measurable compactly supported $w'$ with $\int_{\text{twisted centralizer}} w'(sx)\,d\tau'=1$ whenever $\varphi(x^{-1}\delta\sigma(x))\ne 0$ and $I'=\int\varphi(x^{-1}\delta\sigma(x))\,w'(x)\,d\mu_L(x)$, if and only if there is a nonnegative measurable compactly supported $w$ with $\int_{Z(t)} w(sx)\,d\tau=1$ whenever $\psi(x^{-1}tx)\ne 0$ and $I'=\int\psi(x^{-1}tx)\,w(x)\,d\mu_A(x)$.
--
--   This is the descent identity at the archimedean place for the quadratic extension $\mathbb{C}/\mathbb{R}$: it identifies the twisted orbital integrals of $\varphi$ at the norm element $\delta=\iota(td)$ with the ordinary orbital integrals at $t$ of the descended function $\psi$ obtained by integrating $\varphi$ against the cut-off $\alpha$. It is used by [`AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar`](thm.html#AutomorphicForm.exists_forall_nhds_one_isOrbitalIntegralOn_of_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar), which produces such a descended function on a neighbourhood of the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_conjAe_toTensorGL_mul_scalar_iff_isOrbitalIntegralOn_of_forall_integral_eq_one
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (hι : Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ))
    (t : GL (Fin 2) ℝ) (ht : t = 1 ∨ IsRegularSemisimple t)
    (hT : ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
        ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α) (hα0 : ∀ x, 0 ≤ α x)
    (hαn : ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ≠ 0 →
        ∫ m, α (toTensorGL ℝ ℂ ℝ m * x) ∂μA = 1)
    (ψ : GL (Fin 2) ℝ → ℂ) (hψc : Continuous ψ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∂μL)
    (τ : @Measure (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ t))
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ t) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ')
    (hcpl : Coupled ℝ ℂ ℝ Complex.conjAe t
      (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) 1 τ τ')
    (I' : ℂ) :
    IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ'
        (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' ↔
      IsOrbitalIntegralOn ℝ μA t τ ψ I' := by sorry
