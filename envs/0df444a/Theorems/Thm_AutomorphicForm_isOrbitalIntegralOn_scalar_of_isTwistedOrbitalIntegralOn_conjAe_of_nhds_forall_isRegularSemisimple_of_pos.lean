-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
-- name    : AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/2bf885b4-e347-53b2-bec7-145b6b7ff736
-- title:
--   Archimedean central transfer of matching at a positive scalar
-- statement:
--   Fix Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ (both groups carrying their Borel $\sigma$-algebras), a function $\varphi:\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ and a function $f:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$, each of compact support and each given by a $C^\infty$ function of the matrix entries, and a unit $c\in\mathbb{R}^\times$ with $c>0$. Throughout, $\sigma$ is complex conjugation on $\mathbb{C}$, $N\delta=\delta\cdot\sigma(\delta)$ is `normString`, `IsNormConjugator` $\gamma\,\delta\,y$ says that the image of $\gamma$ in $\mathrm{GL}_2(\mathbb{C}\otimes_\mathbb{R}\mathbb{R})$ equals $y^{-1}(N\delta)y$, the twisted centraliser of $\delta$ is $\{t: t\delta\sigma(t)^{-1}=\delta\}$, `Coupled` says that the pushforward of $\tau'$ along $t\mapsto y^{-1}ty$ coincides with the pushforward of $\tau$ along the base-change embedding, regular semisimplicity of $g$ means that $\operatorname{tr}(g)^2-4\det(g)$ is a unit, and the test function on $\mathrm{GL}_2(\mathbb{C}\otimes_\mathbb{R}\mathbb{R})$ is $\varphi$ transported along the isomorphism $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$. Here an orbital value $I$ of $f$ at $\gamma$ for $(\mu_A,\tau)$ means that for some weight $w\ge 0$, measurable with compact support and satisfying $\int_{Z(\gamma)}w(tx)\,d\tau=1$ whenever $f(x^{-1}\gamma x)\neq 0$, one has $I=\int f(x^{-1}\gamma x)w(x)\,d\mu_A$; a twisted orbital value $I'$ of the transported $\varphi$ at $\delta$ for $(\mu_L,\tau')$ means that $I'=\int\varphi(x^{-1}\delta\,\sigma(x))w(x)\,d\mu_L$ for some $w$ satisfying `IsTwistedSectionFnOn`. The hypothesis is that on some neighbourhood $V$ of the scalar matrix $c\cdot 1$ the two families of integrals agree: for every $\delta$ with $N\delta$ regular semisimple, every regular semisimple $\gamma\in V$, every $y$ with `IsNormConjugator` $\gamma\,\delta\,y$, every Haar pair $(\tau,\tau')$ on the centraliser of $\gamma$ and the twisted centraliser of $\delta$ that is coupled via $y$, and all $I,I'$, a twisted orbital value $I'$ at $\delta$ and an orbital value $I$ at $\gamma$ satisfy $I'=I$. The conclusion extends this to the central point: for every $\delta,y$ with `IsNormConjugator` $(c\cdot 1)\,\delta\,y$, every coupled Haar pair $(\tau,\tau')$ for $(c\cdot 1,\delta,y)$ and every $I'\in\mathbb{C}$, if $I'$ is a twisted orbital value of the transported $\varphi$ at $\delta$ for $(\mu_L,\tau')$, then $I'$ is an orbital value of $f$ at the scalar $c\cdot 1$ for $(\mu_A,\tau)$.
--
--   This is the archimedean local matching statement for $\mathbb{C}/\mathbb{R}$ base change in the first-kind (positive scalar) case: agreement of twisted orbital integrals of $\varphi$ with orbital integrals of $f$ at regular semisimple classes near a positive central element is propagated to the central element itself. It feeds the archimedean comparison of twisted and ordinary orbital integrals, being used by [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar) and by [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_conjAe_of_nhds_forall_isRegularSemisimple_of_pos
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ) (hc : 0 < (c : ℝ))
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
        ∀ I I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) :
    ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
        ∀ I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by sorry
