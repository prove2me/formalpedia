-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
-- name    : AutomorphicForm.integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/bb6fe720-ab77-5742-8b93-76851e64a588
-- title:
--   Convergence of hyperbolic twisted orbital integrals over HbackslashGL₂(mathbb A_L)
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals and let $\Phi_L$ be a set of adelic points of $\mathrm{GL}_2$ over $L$. Fix a Haar measure $\nu_{ZL}$ on $(\mathbb A_L)^\times$ and a set $\Omega_L$ that is a fundamental domain for the image of $L^\times$ in $(\mathbb A_L)^\times$ with respect to $\nu_{ZL}$. Let $D$ be a descent datum, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, acting continuously and compatibly with $L\to\mathbb A_L$, let $\sigma$ generate $\mathrm{Gal}(L/K)$ (every $\tau$ lies in the subgroup of integer powers of $\sigma$), and let $\xi_L:\top\to\mathbb C^\times$ be a character of the idele group that is continuous, trivial on principal ideles and invariant under the automorphism $D.\mathrm{unitsAct}\,\sigma$ of $(\mathbb A_L)^\times$. Let $c,u,d_1,d_2$ be reals with $c>0$, let $T_c$ be compact, and let $\Phi_0$ be contained in the union of the right translates by $y\in T_c$ of the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, all local heights at infinite places at least $c$, all window squares at most $u^2$, all archimedean determinant norms in $[d_1,d_2]$), contained in the slab where the idele norm of $\det g$ lies in $[\alpha,\beta]$, and a fundamental domain for the image of $\mathrm{GL}_2(L)$ for the adelic Haar measure restricted to that slab. Let $H$ be a closed subgroup consisting exactly of those $h$ whose off-diagonal entries $(1,0)$ and $(0,1)$ vanish and for which $\sigma_D(h)h^{-1}$ is central, equipped with a measure $\mu_H$ that is both Haar and right invariant. Let $\delta_0\in\mathrm{GL}_2(L)$ be diagonal with $N_{L/K}(\delta_{0,00}/\delta_{0,11})\neq 1$, and let $\varphi$ be continuous with compact support on $\mathrm{GL}_2(\mathbb A_L)$. Write $F(g)=\int \xi_L(z)\,\varphi\big(g^{-1}\,\delta_0\,\sigma_D(z\cdot g)\big)\,d\nu_{ZL}(z)$, where $\delta_0$ is viewed adelically and $z$ acts through the central scalar embedding. Then, on the quotient of $\mathrm{GL}_2(\mathbb A_L)$ by the orbit relation of $H$ with the quotient measure attached to the adelic Haar measure, $\mu_H$ and $H$, and with $q^{\mathrm{out}}$ a chosen representative of $q$: (1) $q\mapsto F(q^{\mathrm{out}})$ is integrable; (2) $q\mapsto\big(-\log \mathrm{H}(q^{\mathrm{out}})-\log \mathrm{H}(w\,q^{\mathrm{out}})\big)F(q^{\mathrm{out}})$ is integrable, where $\mathrm{H}$ is the adelic height (the product of the archimedean and finite heights) and $w$ is the adelic image of the antidiagonal matrix $!![0,1;1,0]$; and (3) there exists $M\in\mathbb R$ such that $\mathrm{H}(q^{\mathrm{out}})\,\mathrm{H}(w\,q^{\mathrm{out}})\le M$ for every $q$ with $F(q^{\mathrm{out}})\neq 0$.
--
--   This is the analytic input for the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension: the twisted orbital integral of a regular split ($\delta_0$ with $N_{L/K}(\delta_{0,00}/\delta_{0,11})\neq1$) twisted class converges, as does its weighting by the two height logarithms, and the height product is bounded on the set where the integral does not vanish. It is used by the evaluation theorems [`AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn), [`AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn) and [`AutomorphicForm.integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal`](thm.html#AutomorphicForm.integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal), the bound $M$ furnishing the truncation threshold.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integrable_twistedOrbital_and_weighted_and_exists_height_mul_le_of_diagonal_of_norm_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∃ M : ℝ, ∀ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL) ≠ 0 →
        NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L) *
          NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L)) ≤ M := by sorry
