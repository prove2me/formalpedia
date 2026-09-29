-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
-- name    : AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/991c326e-f726-5e34-b53a-b0398ca4db8a
-- title:
--   Twisted orbital integral at a negative central class: sign -1
-- statement:
--   Fix Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ for the Borel $\sigma$-algebras, a function $\varphi$ on $\mathrm{GL}_2(\mathbb{C})$ and a function $f$ on $\mathrm{GL}_2(\mathbb{R})$, each the restriction of a $C^\infty$ function of the matrix entries and of compact support, and a real unit $c$ with $c<0$. Here $\sigma$ is complex conjugation acting on the left factor, the norm of $\delta$ is the product $\delta\,\sigma(\delta)$ of the $\mathrm{finrank}_{\mathbb{R}}\mathbb{C}=2$ twists, $y$ is a norm conjugator for $(\gamma,\delta)$ when the entrywise image $1\otimes\gamma$ equals $y^{-1}\,\delta\sigma(\delta)\,y$, the twisted centralizer of $\delta$ is $\{t\mid t\delta\sigma(t)^{-1}=\delta\}$, and a pair of torus measures is coupled when the pushforward of $\tau'$ under $t\mapsto y^{-1}ty$ equals the pushforward of $\tau$ under $t\mapsto 1\otimes t$. The matching hypothesis asks for a neighbourhood $V$ of the scalar matrix $c\cdot 1$ such that for every $\delta$ with regular semisimple norm (trace${}^2-4\det$ a unit), every regular semisimple $\gamma\in V$, every norm conjugator $y$, and every coupled pair of Haar measures $\tau,\tau'$ on the centralizer of $\gamma$ and the twisted centralizer of $\delta$, any twisted orbital integral $I'$ of $\varphi$ (read through $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$) at $\delta$ against $\mu_L,\tau'$ and any orbital integral $I$ of $f$ at $\gamma$ against $\mu_A,\tau$ agree, $I'=I$. The conclusion: for all $\delta,y$ with $1\otimes(c\cdot 1)=y^{-1}\delta\sigma(\delta)y$ and all Haar $\tau$ on the centralizer of $c\cdot 1$ and Haar $\tau'$ on the twisted centralizer of $\delta$, if the two measures are commonly normalised — there are $\mathbb{R}$-linearly independent tuples $e_1,e_2$ in $M_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ spanning, respectively, the image of $M_2(\mathbb{R})$ under $x\mapsto 1\otimes x$ and the space $\{X\mid X\delta=\delta\,\sigma(X)\}$, and one common $s\in(0,\infty)$, such that the pushforwards of $\tau$ and $\tau'$ to $M_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ are $s$ times the Lebesgue measures in the coordinates $e_1$, $e_2$, each scaled by the square root of the absolute Gram determinant of the form $(X,Y)\mapsto \mathrm{Tr}_{(\mathbb{C}\otimes\mathbb{R})/\mathbb{R}}\,\mathrm{tr}(XY)$ and given the density $|N_{(\mathbb{C}\otimes\mathbb{R})/\mathbb{R}}(\det X)|^{-1}$ — then for every $I'$ that is a twisted orbital integral of $\varphi$ at $\delta$ against $\mu_L,\tau'$, the number $-I'$ is an orbital integral of $f$ at $c\cdot 1$ against $\mu_A,\tau$.
--
--   This is the archimedean base-change comparison for $\mathrm{GL}(2)$ at a real place with $\mathbb{C}/\mathbb{R}$ the quadratic extension, in the case of a negative central class: the norm of $\delta$ being the scalar $c\cdot 1$ with $c<0$ forces the twisted centralizer to be of quaternionic type, no coupled pair of Haar measures exists, and matching of test functions near $c\cdot 1$ transfers with the sign $-1$ rather than $+1$. It feeds the global comparison of twisted and ordinary orbital integrals at central classes used in the degree-two base-change argument, via [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
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
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      (∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
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
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I)) :
    ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) →
        ∀ I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f (-I') := by sorry
