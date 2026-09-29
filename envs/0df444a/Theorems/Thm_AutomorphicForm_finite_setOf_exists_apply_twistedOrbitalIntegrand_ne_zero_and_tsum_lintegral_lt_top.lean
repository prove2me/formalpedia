-- Prove2me | Theorems.Thm_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
-- name    : AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e2d0d2ef-26d6-516b-80f8-b47f907cad53
-- title:
--   Finiteness and convergence of twisted orbital integrands along coset representatives
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z}$ be a Haar measure on the idele group $(\mathbb{A}_L)^\times$ (with its Borel structure), and let $\Omega \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain for $\nu_{Z}$ relative to the image of $L^\times$ under $\operatorname{Units.map}$ of $L \to \mathbb{A}_L$. Let $D$ be an idele Galois descent datum for $L/K$, i.e. a homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $\operatorname{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, continuous and compatible with the action on $L$, and fix $\sigma \in \operatorname{Gal}(L/K)$; write $\sigma_D$ for the induced map on $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma$ entrywise. Let $\xi$ be a homomorphism from the full subgroup $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function is continuous and which is trivial on the image of $L^\times$. Let $\delta_0 \in \mathrm{GL}_2(L)$ have vanishing off-diagonal entries and satisfy $N_{L/K}\big((\delta_0)_{00}/(\delta_0)_{11}\big) \neq 1$. Let $I \subseteq \mathrm{GL}_2(L)$ consist of those $\delta$ for which $\delta_0^{-1}\,g^{-1}\delta\,\sigma(g)$ lies in the centre of $\mathrm{GL}_2(L)$ for some $g$, and let $\Lambda$ be the subgroup of those $\gamma$ with $\delta_0^{-1}\gamma\delta_0\,\sigma(\gamma)^{-1}$ central. Let $\iota$ be countable and $r : \iota \to \mathrm{GL}_2(L)$ a family such that every $\gamma$ satisfies $(r_i)^{-1}\gamma \in \Lambda$ for exactly one $i$. Finally let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support and $x \in \mathrm{GL}_2(\mathbb{A}_L)$. Writing $y_i = \iota(r_i)^{-1}x$ for the image of $r_i$ under the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ and $c(z)$ for the central scalar matrix of an idele $z$, the conclusion is threefold: the set of $i$ for which $\varphi\big(y_i^{-1}\,\iota(\delta_0)\,\sigma_D(c(z)\,y_i)\big) \neq 0$ for some $z \in (\mathbb{A}_L)^\times$ is finite; for every $i$ the lower Lebesgue integral of $z \mapsto \|\xi(z)\,\varphi(y_i^{-1}\,\iota(\delta_0)\,\sigma_D(c(z)\,y_i))\|$ against $\nu_Z$ is finite; and the sum of these integrals over all $i \in \iota$ is finite.
--
--   This is the finiteness and absolute-convergence input needed to unfold the central variable in a twisted $\sigma$-conjugacy contribution to the $\mathrm{GL}_2$ trace formula at a single adelic point $x$, for the regular twisted class of a diagonal $\delta_0$. It is used in the evaluation of the integral of the twisted kernel against a factorisable test function, where term-by-term integration over the coset representatives $r_i$ of $\Lambda$ must be justified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top.lean

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

theorem AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top
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
    {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ,
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠ 0}.Finite ∧
    (∀ i, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤) ∧
    (∑' i, ∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))‖ₑ ∂νZL) < ⊤ := by sorry
