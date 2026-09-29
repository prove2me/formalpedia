-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- name    : AutomorphicForm.setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/2ad98eeb-e168-56a4-afba-3fdf5b8d4a0f
-- title:
--   Vanishing of the central and elliptic fold against a character
-- statement:
--   Let $K$ be a number field, and equip the idele unit group $(\mathbb{A}_K)^\times$ of $K$ (the units of `AdeleRing (𝓞 K) K`) with a measurable structure that is the Borel structure of its topology. Let $\nu_{Z_K}$ be a Haar measure on $(\mathbb{A}_K)^\times$ and let $\Omega_K \subseteq (\mathbb{A}_K)^\times$ be a fundamental domain, in the sense of `IsFundamentalDomain`, for the subgroup given by the image of $K^\times$ under the map induced by $K \to \mathbb{A}_K$. Let $\xi$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is trivial on that image of $K^\times$. Let $\varphi_K$ be an arbitrary complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$, let $z_0 \in (\mathbb{A}_K)^\times$ satisfy $\xi(z_0) \neq 1$, and assume $\varphi_K(g \cdot \mathrm{diag}(z_0,z_0)) = \varphi_K(g)$ for all $g$, where $\mathrm{diag}(z_0,z_0)$ denotes the scalar matrix [`AutomorphicForm.centralScalar (𝓞 K) K z₀`](def/AutomorphicForm_AdelicLsXi.html#L18). Then for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$ the integral over $\Omega_K$, against $\nu_{Z_K}$, of $\xi(z)$ times
--   $$\sum_{\gamma} \varphi_K\bigl(x^{-1} \gamma\, \mathrm{diag}(z,z)\, x\bigr),$$
--   the unordered (finitely supported) sum of $\gamma$ running over those $\gamma \in \mathrm{GL}_2(K)$, embedded entrywise into $\mathrm{GL}_2(\mathbb{A}_K)$, whose underlying matrix satisfies the predicate `IsCentralType`, plus the same sum over those satisfying `IsEllipticType`, equals $0$.
--
--   This is the central-plus-elliptic contribution to an adelic kernel integrated against an idele class character over a fundamental domain for the rational centre; it vanishes by orthogonality of the character, since the test function is invariant under a central element on which the character is non-trivial. It specialises the general vanishing lemma [`NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one`](thm.html#NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one), and is used in the winding computation behind the comparison of hyperbolic terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_centralEllipticPart_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (φK : AdelicGL2 (𝓞 K) K → ℂ)
    (z₀ : (AdeleRing (𝓞 K) K)ˣ) (hz₀ : ξ ⟨z₀, Subgroup.mem_top z₀⟩ ≠ 1)
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, φK (g * AutomorphicForm.centralScalar (𝓞 K) K z₀) = φK g)
    (x : AdelicGL2 (𝓞 K) K) :
    (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (AutomorphicForm.adelicKernelCentralPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
        AutomorphicForm.adelicKernelEllipticPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) = 0 := by sorry
