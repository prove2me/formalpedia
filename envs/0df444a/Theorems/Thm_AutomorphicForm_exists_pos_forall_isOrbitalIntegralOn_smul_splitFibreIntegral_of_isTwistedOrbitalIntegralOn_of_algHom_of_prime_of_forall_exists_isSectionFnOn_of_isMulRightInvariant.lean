-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
-- name    : AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/67f13e8c-906e-55de-a425-a1f823a2ea01
-- title:
--   Split-place transfer of twisted orbital integrals for GL₂
-- statement:
--   Let $K \subseteq L$ be fields with $L/K$ finite of prime degree $\ell = \operatorname{finrank}_K L$, let $\sigma$ be a non-trivial $K$-automorphism of $L$, let $A$ be a commutative topological $K$-algebra which is Hausdorff, locally compact, second countable and has finitely many maximal ideals, and let $\iota : L \to A$ be a $K$-algebra map. Fix Haar measures $\mu_L$ on $\mathrm{GL}_2(L \otimes_K A)$ and $\mu_A$ on $\mathrm{GL}_2(A)$ for the Borel $\sigma$-algebras, assume $\mu_A$ is also right invariant, and assume that for every $\gamma \in \mathrm{GL}_2(A)$ with $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ a unit, every Haar measure $\tau$ on the centraliser of $\gamma$ and every compactly supported $f$ there is a continuous section function $w$ for $f$, i.e. $w \ge 0$, measurable, compactly supported, with $\int_{Z(\gamma)} w(tx)\,d\tau = 1$ whenever $f(x^{-1}\gamma x) \ne 0$. Then there is $c > 0$ such that for every continuous compactly supported $\varphi$ on $\mathrm{GL}_2(L \otimes_K A)$ the following hold, where $F_\varphi =$ `splitFibreIntegral`, the integral of $\varphi$ over the fibres of the split coordinates $\mathrm{GL}_2(L \otimes_K A) \cong \mathrm{GL}_2(A)^{\ell}$ attached to $\iota, \sigma$, the last coordinate being $(g_0 \cdots g_{\ell-2})^{-1}h$. First, for all $\delta$, all $\gamma$ with $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ a unit, all $y$ with $\gamma \otimes 1 = y^{-1}\,(\text{norm string of } \delta)\,y$, all Haar measures $\tau$ on $Z(\gamma)$ and $\tau'$ on the twisted centraliser $\{t : t\delta(\sigma t)^{-1} = \delta\}$ that are coupled (the image of $\tau'$ under $t \mapsto y^{-1}ty$ equals the image of $\tau$ under $t \mapsto t \otimes 1$), every value $I' = \int \varphi(x^{-1}\delta\,\sigma(x))w(x)\,d\mu_L$ of a twisted orbital integral of $\varphi$ at $\delta$ is an orbital integral of $c \cdot F_\varphi$ at $\gamma$ with respect to $\tau$ and $\mu_A$. Second, in the central case $\gamma = z \cdot 1$ with $z \in A^\times$, under the same coupling hypotheses and if the pushforward of $\tau$ to $\mathrm{GL}_2(A)$ is $c_0 \cdot \mu_A$ for some $c_0 \in \mathbb{R}_{\ge 0}$, every such $I'$ equals $c\,F_\varphi(z \cdot 1)\,c_0^{-1}$.
--
--   This is the local matching of orbital integrals for cyclic base change of $\mathrm{GL}_2$ at a place splitting completely in $L/K$: twisted orbital integrals of $\varphi$ on $\mathrm{GL}_2(L \otimes_K A)$ are realised as orbital integrals of the fibre integral of $\varphi$, with the central classes handled by the same change of variables. It is the general form from which the archimedean transfer statements at complex and at real places are deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [Finite (MaximalSpectrum A)]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA)

    (hsec : ∀ γ : GL (Fin 2) A, AutomorphicForm.IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
      ∀ f : GL (Fin 2) A → ℂ, HasCompactSupport f →
        ∃ w : GL (Fin 2) A → ℝ, AutomorphicForm.IsSectionFnOn A γ τ f w ∧ Continuous w)

    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (AutomorphicForm.glBorelOf A) _ μA) :
    ∃ c : ℝ, 0 < c ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] A) → ℂ, Continuous φ → HasCompactSupport φ →
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (γ : GL (Fin 2) A), AutomorphicForm.IsRegularSemisimple γ →
          ∀ y : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormConjugator K L A σ γ δ y →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A γ))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel A γ) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ γ δ y τ τ' →
            ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
              AutomorphicForm.IsOrbitalIntegralOn A μA γ τ
                (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ) I') ∧
        (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ) (y : GL (Fin 2) (L ⊗[K] A)),
          AutomorphicForm.IsNormConjugator K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y →
          ∀ (τ : @Measure (Subgroup.centralizer
                  ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
                (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
            (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
                (AutomorphicForm.twistedCentralizerBorel K L A σ δ)),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) τ →
            @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' →
            AutomorphicForm.Coupled K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) δ y τ τ' →
            ∀ c₀ : NNReal,
              @Measure.map _ _
                  (AutomorphicForm.centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
                  (AutomorphicForm.glBorelOf A) Subtype.val τ = c₀ • μA →
              ∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
                I' = (c • AutomorphicForm.splitFibreIntegral K L hdeg σ hσ A ι μA φ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * ((((c₀ : ℝ))⁻¹ : ℝ) : ℂ)) := by sorry
