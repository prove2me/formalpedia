-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg
-- name    : AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/884e2aed-07ba-530d-97c4-2afbebfdef09
-- title:
--   Negative central scalar: twisted orbital integral equals minus orbital integral
-- statement:
--   Work with the Borel $\sigma$-algebras on $\mathrm{GL}_2(\mathbb R)$, on $\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ and on the relevant centralisers. Let $\mu_A$ and $\mu_L$ be Haar measures on $\mathrm{GL}_2(\mathbb R)$ and $\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$; let $\varphi$ on $\mathrm{GL}_2(\mathbb C)$ and $f$ on $\mathrm{GL}_2(\mathbb R)$ each be the restriction to invertible matrices of a $C^\infty$ function of the matrix entries, with compact support; let $c$ be a unit of $\mathbb R$ with $c<0$. The twist is $\sigma=$ complex conjugation acting on the left factor of $\mathbb C\otimes_{\mathbb R}\mathbb R$, and $\mathrm{normString}$ is the product $\delta\,\sigma(\delta)$ over the $\operatorname{finrank}_{\mathbb R}\mathbb C$ iterates of $\sigma$. Assume the matching hypothesis: there is a neighbourhood $V$ of the scalar matrix $c\cdot 1$ such that (i) whenever $\mathrm{normString}(\delta')$ is regular semisimple in the sense that $\operatorname{tr}^2-4\det$ is a unit, $\gamma\in V$ is regular semisimple, $y$ satisfies $1\otimes\gamma=y^{-1}\,\mathrm{normString}(\delta')\,y$, and Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the twisted centraliser $\{t\mid t\delta'\sigma(t)^{-1}=\delta'\}$ are coupled (the pushforward of $\tau'$ under $t\mapsto y^{-1}ty$ equals the pushforward of $\tau$ under $t\mapsto 1\otimes t$), every twisted orbital integral of $\varphi$, read through $\mathbb C\otimes_{\mathbb R}\mathbb R\cong\mathbb C$, at $\delta'$ against $\mu_L,\tau'$ equals every orbital integral of $f$ at $\gamma$ against $\mu_A,\tau$; and (ii) for regular semisimple $\gamma\in V$ that are the norm of no $\delta'$, every orbital integral of $f$ at $\gamma$ vanishes. The conclusion: for all $\delta,y$ with $1\otimes(c\cdot 1)=y^{-1}\,\mathrm{normString}(\delta)\,y$, and all Haar measures $\tau$ on the centraliser of $c\cdot 1$ and $\tau'$ on the twisted centraliser of $\delta$ satisfying the common Gram normalisation — there exist $\mathbb R$-bases $e_1$ of the image of $M_2(\mathbb R)$ under $x\mapsto 1\otimes x$ and $e_2$ of $\{X\mid X\delta=\delta\,\sigma(X)\}$, and a scalar $s\in(0,\infty)$, such that the pushforwards of $\tau$ and $\tau'$ to $M_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ are both $s$ times the Lebesgue measure in the given coordinates, scaled by $\sqrt{|\det(\operatorname{Tr}_{(\mathbb C\otimes\mathbb R)/\mathbb R}\operatorname{tr}(e_ie_j))|}$ and given density $|N_{(\mathbb C\otimes\mathbb R)/\mathbb R}(\det X)|^{-1}$ — every $I'$ that is a twisted orbital integral of $\varphi$ at $\delta$ against $\mu_L,\tau'$ has $-I'$ an orbital integral of $f$ at $c\cdot 1$ against $\mu_A,\tau$.
--
--   This is the archimedean base-change comparison at a real place of the base field that becomes complex above, for a central class $c\cdot 1$ with $c<0$: such a $c$ is not a norm $z\bar z$, the twisted centraliser is the unit group of the Hamilton quaternions, no coupling of Haar measures is available, and the two tori are instead normalised by one common Gram rule; the resulting comparison carries the sign $-1$. It feeds the global degree-two statement [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isRegularSemisimple_of_neg
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
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) ∧
      (∀ γ ∈ V, IsRegularSemisimple γ →
        (¬ ∃ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ f I → I = 0)) :
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
