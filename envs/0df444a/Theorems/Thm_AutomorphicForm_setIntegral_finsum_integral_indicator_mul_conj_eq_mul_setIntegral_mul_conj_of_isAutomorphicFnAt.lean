-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
-- name    : AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e0b93175-cc12-5f57-8385-63bbedc9aad6
-- title:
--   Unfolding an automorphised test function against an automorphic function
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Fix a Borel measurable structure on the idele class group's ambient group $(\mathbb A_K)^\times$, a Haar measure $\nu_{Z}$ on $(\mathbb A_K)^\times$, and a set $\Omega\subseteq(\mathbb A_K)^\times$ that is a fundamental domain for the action of the image of $K^\times\to(\mathbb A_K)^\times$ (the range of the induced map on units) with respect to $\nu_Z$. Let $\xi$ be a homomorphism from the full subgroup $\top\le(\mathbb A_K)^\times$ to $\mathbb C^\times$ whose associated complex-valued function is continuous, which takes the value $1$ on the image of $K^\times$, and all of whose values have absolute value $1$. Let $\Psi:GL_2(\mathbb A_K)\to\mathbb C$ be measurable, vanishing outside some compact set, and bounded, and let $u:GL_2(\mathbb A_K)\to\mathbb C$ satisfy `IsAutomorphicFnAt` for $\xi$ and for the carrier data `productionPinsOf` attached to the domain `canonicalTruncationDomain K α β`, the level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M` intersected with the kernel of the archimedean component map, the local Hecke generators `heckeGen`, and the box `adelicBox K`; that is, $u$ satisfies the predicate `LsXiMember` for the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $GL_2(\mathbb A_K)$, the subgroup $\top\le(\mathbb A_K)^\times$, the character $\xi$ and the domain `canonicalTruncationDomain K α β` (the set component of a chosen truncation datum for $(\alpha,\beta)$, empty if none exists). Then, with $\Phi_0=$ `canonicalTruncationDomain K α β` and all integrals over $GL_2(\mathbb A_K)$ taken with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`,
--   $$\int_{\Phi_0}\Big(\sum_{q\in GL_2(K)/Z(GL_2(K))}^{\mathrm f}\ \int_{(\mathbb A_K)^\times}\xi(w)^{-1}\,\big(\mathbf 1_{\Phi_0}\Psi\big)\big(w\cdot(\gamma_q\, g)\big)\,d\nu_Z(w)\Big)\,\overline{u(g)}\,dg =\;b\int_{\Phi_0}\Psi(g)\,\overline{u(g)}\,dg,$$
--   where the inner sum is a finite-support sum over cosets $q$, $\gamma_q$ denotes `globalPoints` applied to a chosen representative `q.out`, $w$ acts through the central scalar matrix `centralScalar (𝓞 K) K w`, and the constant is $b=\nu_Z\big(\Omega\cap\{z\mid \mathrm{ideleNorm}_K(\det(\mathrm{centralScalar}\,z))\in[\alpha,\beta]\}\big)$, converted to a real number and then to a complex scalar (here $\det$ of the scalar matrix attached to $z$ is $z^2$).
--
--   This is the unfolding identity for the $(GL_2(K),(\mathbb A_K)^\times,\xi)$-automorphisation of a compactly supported test function: pairing the automorphised kernel with an automorphic function over the truncation domain returns the pairing of the test function itself, multiplied by the measure of the determinant band cut out of the fundamental domain $\Omega$. It is used in the computation of the matrix coefficients of convolution operators, in particular in the identification of their continuous and residual projections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
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
    (u : AdelicGL2 (𝓞 K) K → ℂ)
    (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) :
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
