-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
-- name    : AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/df067e48-3703-5954-b076-75311f07c86b
-- title:
--   Central transfer at a split real place
-- statement:
--   Let $K\subseteq L$ be fields with $L$ finite-dimensional over $K$ of prime degree $n=\operatorname{finrank}_K L$, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma\neq 1$, let $\mathbb{R}$ be a $K$-algebra and $\iota\colon L\to\mathbb{R}$ a $K$-algebra map. Let $\mu_A$ be a Haar measure on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ one on $\mathrm{GL}_2(L\otimes_K\mathbb{R})$, both for the Borel $\sigma$-algebra. Assume $\varphi\colon\mathrm{GL}_2(L\otimes_K\mathbb{R})\to\mathbb{C}$ has compact support and is of the form $\varphi(g)=\Phi\big((\psi_k(g)_{ij})\big)$ for some $C^\infty$ function $\Phi$ of the $n$ blocks of matrix entries obtained from the splitting isomorphism `SplitPlace.psiGL` attached to $\sigma,\iota$, and that $f\colon\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ has compact support and is $C^\infty$ in the matrix entries. Let $c\in\mathbb{R}^\times$ and write $z=c\cdot 1$ for the corresponding scalar element of $\mathrm{GL}_2(\mathbb{R})$. The matching hypothesis asserts the existence of a neighbourhood $V$ of $z$ such that: whenever the norm string $N(\delta)=\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ is regular semisimple (that is, $\operatorname{tr}^2-4\det$ is a unit), $\gamma\in V$ is regular semisimple, $y$ satisfies $\gamma\otimes 1=y^{-1}N(\delta)y$, $\tau$ is a Haar measure on the centraliser of $\gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and $\tau'$ a Haar measure on the $\sigma$-twisted centraliser $\{t: t\delta\sigma(t)^{-1}=\delta\}$, the two are coupled (the image of $\tau'$ under $t\mapsto y^{-1}ty$ equals the image of $\tau$ under $t\mapsto t\otimes 1$), and $I'$, $I$ are respectively a value of the twisted orbital integral $\int\varphi(x^{-1}\delta\,\sigma(x))w(x)\,d\mu_L$ for a twisted section function $w$ in the sense of `IsTwistedSectionFnOn`, and a value of the orbital integral $\int f(x^{-1}\gamma x)w(x)\,d\mu_A$ for a section function $w$ (non-negative, measurable, compactly supported, with $\int w(tx)\,d\tau=1$ over the centraliser whenever $f(x^{-1}\gamma x)\neq 0$), then $I'=I$. The conclusion is that for all $\delta,y$ with $z\otimes 1=y^{-1}N(\delta)y$, all Haar measures $\tau$ on the centraliser of $z$ and $\tau'$ on the twisted centraliser of $\delta$ that are coupled via $y$, and every $I'$ which is a twisted orbital integral value of $\varphi$ at $\delta$ against $\tau'$, the number $I'$ is also an orbital integral value of $f$ at the scalar $z$ against $\tau$.
--
--   This is the archimedean split-place central identity for base change of $\mathrm{GL}(2)$: matching of $\varphi$ and $f$ at the regular semisimple classes near a scalar propagates to the central class itself, so that twisted orbital values at $\delta$ with central norm are orbital values of $f$ at that scalar. It is used by [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar) and by [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hdeg hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport φ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
        Coupled K L ℝ σ γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) :
    ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
      IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
        Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
        ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by sorry
