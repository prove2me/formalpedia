-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives
-- name    : AutomorphicForm.integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9353f728-e7ad-5a1c-b0b0-b7a04b3401ea
-- title:
--   Unfolding one twisted hyperbolic class into orbital integrals
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $\nu_{ZL}$ be a Haar measure on the idele unit group $(\mathbb{A}_L)^\times$ (taken with its Borel structure), and let $\Omega_L$ be a fundamental domain for the action of the image of $L^\times$ under `Units.map` of $L \to \mathbb{A}_L$. Let $D$ consist of a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous in each $g$, and let $\sigma \in \mathrm{Gal}(L/K)$; write $\sigma_D$ for the entrywise action of $D.\mathrm{act}\,\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $\iota$ for the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$, and $c(z)$ for the scalar matrix with diagonal entry $z$. Let $\xi_L$ be a homomorphism from the full subgroup $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function is continuous and which is trivial on principal ideles (no $\sigma$-invariance is assumed). Let $\delta_0 \in \mathrm{GL}_2(L)$ have vanishing $(1,0)$ and $(0,1)$ entries, with $N_{L/K}(\delta_{0,00}/\delta_{0,11}) \neq 1$; let $I$ be the set of $\delta$ for which some $g \in \mathrm{GL}_2(L)$ satisfies $\delta_0^{-1} g^{-1} \delta\, \sigma(g)$ central, and $\Lambda$ the subgroup of $\gamma$ with $\delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}$ central; let $r : \iota \to \mathrm{GL}_2(L)$, with $\iota$ countable, be such that every $\gamma$ lies in $r_i\Lambda$ for exactly one $i$. Let $\varphi$ be continuous with compact support on $\mathrm{GL}_2(\mathbb{A}_L)$ and let $x \in \mathrm{GL}_2(\mathbb{A}_L)$; put $y_i = \iota(r_i)^{-1}x$. Then, first, in $[0,\infty]$ the lower integral over $\Omega_L$ of $\sum_{\delta \in I}\|\xi_L(z)\varphi(x^{-1}\iota(\delta)\sigma_D(c(z)x))\|$ equals $\sum_i$ of the lower integral over all of $(\mathbb{A}_L)^\times$ of $\|\xi_L(z)\varphi(y_i^{-1}\iota(\delta_0)\sigma_D(c(z)y_i))\|$; and secondly, if that iterated sum of lower integrals is finite, then $z \mapsto \xi_L(z)\sum^{\mathrm{f}}_{\delta \in I}\varphi(x^{-1}\iota(\delta)\sigma_D(c(z)x))$ (a finitary sum over $I$) is integrable on $\Omega_L$, the family of Bochner integrals $F_i = \int \xi_L(z)\varphi(y_i^{-1}\iota(\delta_0)\sigma_D(c(z)y_i))\,d\nu_{ZL}$ over $(\mathbb{A}_L)^\times$ is summable, and $\int_{\Omega_L}\xi_L(z)\sum^{\mathrm{f}}_{\delta\in I}\varphi(x^{-1}\iota(\delta)\sigma_D(c(z)x))\,d\nu_{ZL} = \sum_i F_i$.
--
--   This is the unfolding step for a single regular ($\sigma$-)hyperbolic twisted class in the twisted trace formula for $\mathrm{GL}_2$: the kernel attached to the class $I$, integrated against $\xi_L$ over a fundamental domain modulo principal ideles, is rewritten as a sum of twisted orbital integrals of $\varphi$ at $\delta_0$ over representatives of $\Lambda$-cosets. It is the kernel half of the geometric-side computation used by [`AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_sigmaConjClassOrbit_sub_indicator_constantTerm_eq_setIntegral_tsum_weight_mul_integral_of_isFactorizableTestFn), and rests on the orbit–stabiliser transport statement [`AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives`](thm.html#AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives) together with [`AutomorphicForm.adelicKernelLocalFiniteness`](thm.html#AutomorphicForm.adelicKernelLocalFiniteness).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives.lean

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

theorem AutomorphicForm.integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    (∫⁻ z in ΩL, ∑' δ : I, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (δ : GL (Fin 2) L) *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ ∂νZL =
      ∑' i, ∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) ∧
    ((∑' i, ∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤ →
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))) ΩL νZL ∧
      Summable (fun i => ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) ∧
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ I, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL =
        ∑' i, ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL) := by sorry
