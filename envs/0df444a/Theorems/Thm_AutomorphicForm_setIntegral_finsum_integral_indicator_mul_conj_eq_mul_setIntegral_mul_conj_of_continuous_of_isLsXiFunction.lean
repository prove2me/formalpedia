-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
-- name    : AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fc005879-f581-5966-9a4e-adeaa85b9735
-- title:
--   Unfolding an automorphisation against a continuous ξ-equivariant function
-- statement:
--   Let $K$ be a number field and $\alpha,\beta$ reals with $0<\alpha$ and $\alpha<\beta$; the unit group $(\mathbb{A}_K)^\times$ of the adele ring carries a measurable structure which is the Borel structure, and $\nu_{Z}$ is a Haar measure on it. Let $\Omega$ be a set that is a fundamental domain, with respect to $\nu_{Z}$, for the action of the image of $K^\times$ in $(\mathbb{A}_K)^\times$ under the map induced by $K \to \mathbb{A}_K$. Let $\xi$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated function $z \mapsto \xi(z)$ is continuous, which takes the value $1$ on the image of $K^\times$, and satisfies $\|\xi(z)\|=1$ for all $z$. Let $\Psi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be measurable, vanishing outside some compact set, and bounded in norm by some constant. Let $u : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and satisfy `IsLsXiFunction` for $\top$ and $\xi$, i.e. $u(\gamma g) = u(g)$ for every $\gamma \in \mathrm{GL}_2(K)$ embedded adelically, and $u(zg) = \xi(z)\,u(g)$ for every idele $z$ acting through the scalar matrix. Write $\Phi_0$ for the canonical truncation domain `canonicalTruncationDomain K α β`, the domain component of the canonically chosen truncation datum attached to the determinant window $[\alpha,\beta]$. Then the integral over $\Phi_0$, against the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, of
--   $$\Big(\textstyle\sum^{\mathrm{f}}_{q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))} \int_{(\mathbb{A}_K)^\times} \xi(w)^{-1}\,(\mathbf 1_{\Phi_0}\Psi)\big(w\,\gamma_q\,g\big)\,d\nu_{Z}(w)\Big)\,\overline{u(g)},$$
--   where $\gamma_q$ is the chosen representative `q.out` of $q$ embedded adelically and the outer sum is a finitely supported sum, equals the real number $\nu_{Z}\big(\Omega \cap \{z \mid \text{the idele norm of } \det(zI) \in [\alpha,\beta]\}\big)$, coerced to $\mathbb{C}$, times $\int_{\Phi_0} \Psi(g)\,\overline{u(g)}$ with respect to the same measure.
--
--   This is the unfolding identity for the automorphisation of a compactly supported test function on $\mathrm{GL}_2(\mathbb{A}_K)$ paired against a left $\mathrm{GL}_2(K)$-invariant, centrally $\xi$-equivariant function: the pairing collapses to the pairing of $\Psi$ itself, multiplied by the volume of the determinant band in the idele class group. It is the variant of [`AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt) in which the partner $u$ is merely continuous rather than square-integrable on the truncation domain (the case relevant to Eisenstein series on the unitary axis), and it feeds the later results on continuation along the axis and on the spectral expansion of the truncated pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_huc : Continuous u)
    (_hu : IsLsXiFunction (𝓞 K) K ⊤ ξK u) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, Ψ g * conj (u g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
