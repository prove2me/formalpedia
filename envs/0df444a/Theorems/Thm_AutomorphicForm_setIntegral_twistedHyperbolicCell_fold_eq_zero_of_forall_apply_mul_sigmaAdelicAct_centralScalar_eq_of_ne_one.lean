-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one
-- name    : AutomorphicForm.setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0bb5e2f0-4638-5855-9cf6-642be466f6b6
-- title:
--   Vanishing of the twisted hyperbolic ξ_L-fold over a fundamental domain
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and let $\Phi_L$ be a set of matrices in $GL_2(\mathbb{A}_L)$. Fix a Borel measurable structure on the idele units $(\mathbb{A}_L)^\times$, a Haar measure $\nu_{Z_L}$ on it, and a set $\Omega_L$ that is a fundamental domain for the action of the image of $L^\times$ under $\mathrm{Units.map}$ of $L \to \mathbb{A}_L$ with respect to $\nu_{Z_L}$. Let $D$ be a datum [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each argument and compatible with $L \to \mathbb{A}_L$; write $\sigma_D$ for the induced automorphism of $GL_2(\mathbb{A}_L)$ obtained by applying $D(\sigma)$ entrywise. Let $\xi_L$ be a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ which is trivial on the principal ideles, let $\varphi_L : GL_2(\mathbb{A}_L) \to \mathbb{C}$, and let $z_0$ be an idele unit with $\xi_L(z_0) \neq 1$ such that $\varphi_L(g \cdot \sigma_D(z_0 I)) = \varphi_L(g)$ for all $g$, where $z_0 I$ denotes the central scalar matrix. Then for every real $R$ and every $x \in GL_2(\mathbb{A}_L)$, the integral over $\Omega_L$ against $\nu_{Z_L}$ of $\xi_L(z)$ times the difference of the following two terms vanishes: first, the finite sum over those $\delta \in GL_2(L)$ whose $\sigma$-twisted conjugacy class is sent by [`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766) to the ordinary conjugacy class of some $\gamma \in GL_2(K)$ whose characteristic polynomial splits over $K$ with two distinct roots, of $\varphi_L(x^{-1} \cdot \delta \cdot \sigma_D(zI \cdot x))$, the image of $\delta$ in $GL_2(\mathbb{A}_L)$ being taken entrywise; second, the value at $zI \cdot x$ of the indicator function of the set of $g$ with $\exp R < H_L(g)$, where $H_L$ is the adelic height of $L$ (the product of the archimedean and finite local heights), multiplied by the constant term $\int \Psi(u(t) \cdot zI \cdot x)\, d\nu(t)$, where $u(t)$ is the upper unipotent matrix with entry $t$, $\nu$ is the additive Haar measure of $\mathbb{A}_L$ conditioned on `adelicBox L` (the measure component of the package `productionPinsOf` built from $\Phi_L$, the levels $\mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box), and $\Psi(y)$ is the finite sum over those $\delta \in GL_2(L)$ with lower-left entry $0$ and $N_{L/K}(\delta_{00}/\delta_{11}) \neq 1$ of $\varphi_L(x^{-1} \cdot \delta \cdot \sigma_D(y))$.
--
--   This is the $\sigma$-twisted counterpart of the vanishing of the hyperbolic fold of a kernel against an idele class character: invariance of $\varphi_L$ under right translation by the $\sigma$-twist of a central scalar $z_0$ with $\xi_L(z_0) \neq 1$ forces the $\xi_L$-weighted integral of the truncated twisted hyperbolic term over a fundamental domain for $L^\times$ in the ideles to vanish. It feeds the extraction of the affine shape of the hyperbolic contribution in the twisted trace formula comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindingDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_twistedHyperbolicCell_fold_eq_zero_of_forall_apply_mul_sigmaAdelicAct_centralScalar_eq_of_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φL : AdelicGL2 (𝓞 L) L → ℂ)
    (z₀ : (AdeleRing (𝓞 L) L)ˣ) (hz₀ : ξL ⟨z₀, Subgroup.mem_top z₀⟩ ≠ 1)
    (hφ : ∀ g : AdelicGL2 (𝓞 L) L,
      φL (g * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z₀)) = φL g)
    (R : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) = 0 := by sorry
