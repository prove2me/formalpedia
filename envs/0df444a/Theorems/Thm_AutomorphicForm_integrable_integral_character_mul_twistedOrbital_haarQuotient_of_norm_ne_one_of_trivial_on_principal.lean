-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal
-- name    : AutomorphicForm.integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/75920239-42fd-564c-a6f7-9431ea0004db
-- title:
--   Integrability of a twisted orbital integral at a regular class
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\nu_{Z_L}$ be a Haar measure on the idele units $(\mathbb{A}_L)^\times$ (with its Borel structure). Let $D$ be an `IdeleGaloisDescent` datum for $L/K$, that is a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, each continuous and compatible with $L \to \mathbb{A}_L$, and let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ whose integral powers exhaust the group. Let $\xi_L$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi_L(z)$ is continuous as a $\mathbb{C}$-valued function, invariant under the automorphism of $(\mathbb{A}_L)^\times$ induced by $\sigma$ through $D$, and trivial on the image of $L^\times$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which the entrywise image $\sigma(h)$ under $D(\sigma)$ satisfies $\sigma(h)h^{-1} \in Z(\mathrm{GL}_2(\mathbb{A}_L))$, and let $\mu_H$ be a measure on $H$ that is both a Haar measure and right invariant. Let $t \in \mathrm{GL}_2(L)$ have vanishing $(1,0)$ and $(0,1)$ entries with $N_{L/K}(t_{00}/t_{11}) \neq 1$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support. Then the function on the quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by the orbit relation of $H$ sending an orbit $q$, with chosen representative $q.\mathrm{out}$, to
--   $$\int \xi_L(z)\,\varphi\bigl(q.\mathrm{out}^{-1}\, t\, \sigma(z\cdot q.\mathrm{out})\bigr)\, d\nu_{Z_L}(z),$$
--   where $t$ is viewed in $\mathrm{GL}_2(\mathbb{A}_L)$ entrywise and $z$ as the scalar matrix $z\cdot I$, is integrable for the measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28), the pushforward to the orbit quotient of the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ weighted by the density attached to $H$ and $\mu_H$.
--
--   This is the convergence statement for the $\xi_L$-twisted orbital integral of a test function at a regular ($N_{L/K}(t_{00}/t_{11}) \neq 1$) diagonal class, taken over the quotient by the $\sigma$-twisted centraliser $H$; it is the analytic input needed before such orbital integrals can be compared or summed. It is used in the estimate [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrable_integral_character_mul_twistedOrbital_haarQuotient_of_norm_ne_one_of_trivial_on_principal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
      ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by sorry
