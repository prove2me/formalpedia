-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
-- name    : AutomorphicForm.lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c9d69bdd-0a8f-5b30-b52c-0bcff3cc549d
-- title:
--   Lower integral equals real part of orbital double integral
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let the unit group $(\mathbb{A}_L)^\times$ of the adele ring of $L$ carry a Borel measurable structure and a Haar measure $\nu_{Z_L}$, and let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) for $\mathcal{O}_L$, $K$, $L$, i.e. a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to continuous ring automorphisms of $\mathbb{A}_L$ extending the action on $L$. Fix $\sigma \in \mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, and let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose members are exactly the $h$ with $h_{10} = h_{01} = 0$ and $\mathrm{sigmaAdelicAct}(h)\,h^{-1}$ central, where $\mathrm{sigmaAdelicAct}$ acts on matrices entrywise through $D.\mathrm{act}\,\sigma$; let $\mu_H$ be a right-invariant Haar measure on $H$. Let $t \in \mathrm{GL}_2(L)$ satisfy $t_{10} = t_{01} = 0$ and $N_{L/K}(t_{00}/t_{11}) \neq 1$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support and with $\varphi(g)$ real and nonnegative for all $g$. Write $F(q) = \int \varphi\bigl(q^{-1}\,t\,\mathrm{sigmaAdelicAct}(z\cdot q)\bigr)\,d\nu_{Z_L}(z)$, where $q$ runs over the quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by the orbit relation of $H$ with chosen representatives, $t$ is the image of $t$ under the entrywise map $L \to \mathbb{A}_L$, and $z$ is viewed as the scalar matrix with diagonal $z$; assume $F$ is integrable for the quotient measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28), the pushforward to the quotient of the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ weighted by the density attached to $H$ and $\mu_H$. Then the iterated lower integral over the quotient, of the inner lower integral of $\mathrm{ofReal}\,\|\varphi(q^{-1}t\,\mathrm{sigmaAdelicAct}(zq))\|$ against $\nu_{Z_L}$, equals $\mathrm{ofReal}$ of the real part of the corresponding iterated Bochner integral.
--
--   This is the passage from unsigned lower (Lebesgue) integrals to Bochner integrals for the hyperbolic orbital term attached to the regular element $t$ and the $\sigma$-twisted action, valid because the test function is real and nonnegative. It is used in the derivation of the bound [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), where the unsigned iterated integral is estimated and then identified with the genuine double integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg.lean

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

theorem AutomorphicForm.lintegral_lintegral_ofReal_norm_twistedOrbital_eq_ofReal_re_integral_integral_of_nonneg
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : ∀ g : AdelicGL2 (𝓞 L) L, 0 ≤ (φ g).re ∧ (φ g).im = 0)
    (hint : Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
          (∫ z, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) :
    (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
          (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) =
      ENNReal.ofReal
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ z, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)).re := by sorry
