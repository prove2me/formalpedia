-- Prove2me | Theorems.Thm_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
-- name    : AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/5df73042-f0ba-5c5a-85b8-3cb25ef7ec86
-- title:
--   Twisted orbit parametrised by coset representatives and central scalars
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $D$ be a datum consisting of a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ which is continuous in each component and compatible with $L \to \mathbb{A}_L$, and let $\sigma \in \mathrm{Gal}(L/K)$. Fix $\delta_0 \in \mathrm{GL}_2(L)$ with vanishing off-diagonal entries and with $N_{L/K}((\delta_0)_{00}/(\delta_0)_{11}) \neq 1$. Let $I \subseteq \mathrm{GL}_2(L)$ be a set whose members are exactly the $\delta$ for which $\delta_0^{-1} g^{-1} \delta \,\sigma(g)$ is central for some $g \in \mathrm{GL}_2(L)$, where $\sigma$ acts entrywise, and let $\Lambda \le \mathrm{GL}_2(L)$ be a subgroup whose members are exactly the $\gamma$ with $\delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}$ central. Let $\iota$ be a countable type and $r : \iota \to \mathrm{GL}_2(L)$ be such that every $\gamma$ satisfies $(r_i)^{-1}\gamma \in \Lambda$ for a unique $i$. Then: (i) $r_i\,\delta_0\,\zeta I_2\,\sigma(r_i)^{-1} \in I$ for all $i$ and all $\zeta \in L^\times$; (ii) each $\delta \in I$ is of this form for a unique pair $(i,\zeta) \in \iota \times L^\times$; (iii) writing $\iota(\cdot)$ for the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$, $c(\cdot)$ for the scalar embedding of $\mathbb{A}_L^\times$ and $\sigma_D$ for the entrywise action of $D(\sigma)$, one has, for all $i$, $\zeta \in L^\times$, $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and $z \in \mathbb{A}_L^\times$, $$x^{-1}\,\iota\!\left(r_i\delta_0\zeta I_2\sigma(r_i)^{-1}\right)\,\sigma_D(c(z)x) = y^{-1}\,\iota(\delta_0)\,\sigma_D\!\left(c\big(D(\sigma^{-1})(\hat\zeta)\,z\big)\,y\right), \qquad y = \iota(r_i)^{-1}x,$$ where $\hat\zeta$ is the image of $\zeta$ in $\mathbb{A}_L^\times$.
--
--   This is the indexing device for a $Z(L)$-saturated twisted $\sigma$-conjugacy orbit of a regular diagonal element: the orbit is in bijection with pairs (coset representative modulo the twisted centraliser, central scalar), and the displayed identity transports the kernel integrand attached to a member of the orbit to the one attached to $\delta_0$. It is used in the unfolding of the class kernel for such an orbit, in the convergence statement [`AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top`](thm.html#AutomorphicForm.finite_setOf_exists_apply_twistedOrbitalIntegrand_ne_zero_and_tsum_lintegral_lt_top) and in the term-by-term integration statement [`AutomorphicForm.integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives`](thm.html#AutomorphicForm.integrableOn_finsum_sigmaConjClassOrbit_and_setIntegral_eq_tsum_integral_of_leftCosetRepresentatives).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives.lean

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

theorem AutomorphicForm.mem_sigmaConjClassOrbit_and_existsUnique_and_transport_of_leftCosetRepresentatives
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ) :
    (∀ (i : ι) (ζ : Lˣ),
      r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i))⁻¹ ∈ I) ∧
    (∀ δ ∈ I, ∃! p : ι × Lˣ,
      δ = r p.1 * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r p.1))⁻¹) ∧
    (∀ (i : ι) (ζ : Lˣ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L
          (r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i))⁻¹) *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
      ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L
              (D.unitsAct σ⁻¹ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) ζ) * z) *
            ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) := by sorry
