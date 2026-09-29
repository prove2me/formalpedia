-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul
-- name    : AutomorphicForm.continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/99c57a60-53e2-5300-8a1c-6c9cf92be2aa
-- title:
--   Continuity and equivariance of the centre-folded GL₂ kernel
-- statement:
--   Let $K$ be a number field, write $\mathbb{A} = \mathrm{AdeleRing}(\mathcal{O}_K,K)$, and fix a Haar measure $\nu_{Z}$ on the topological group $\mathbb{A}^{\times}$ (taken with its Borel structure). Let $\xi$ be a homomorphism from the full subgroup $\top \le \mathbb{A}^{\times}$ to $\mathbb{C}^{\times}$ such that $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function on $\mathbb{A}^{\times}$ and $\xi(z) = 1$ for every $z$ in the image of $K^{\times} \to \mathbb{A}^{\times}$ induced by the structure map $K \to \mathbb{A}$; let $f : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be continuous with compact support. Consider the two-variable expression $$K_f(x,y) = \sum_{q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}^{\mathrm{fin}} \int_{\mathbb{A}^{\times}} \xi(z)\, f\bigl(x^{-1}\,\gamma_q\,(z\cdot y)\bigr)\, d\nu_{Z}(z),$$ where $\gamma_q \in \mathrm{GL}_2(\mathbb{A})$ is the entrywise image of a chosen representative of the class $q$ under $K \to \mathbb{A}$, and $z \cdot y$ means the product of the scalar matrix $\mathrm{diag}(z,z)$ with $y$; the outer sum is a finite-support sum over the quotient of $\mathrm{GL}_2(K)$ by its centre. The conclusion is the conjunction of five assertions: the map $(x,y) \mapsto K_f(x,y)$ is continuous on $\mathrm{GL}_2(\mathbb{A}) \times \mathrm{GL}_2(\mathbb{A})$; for all $\gamma \in \mathrm{GL}_2(K)$ and all $x,y$ one has $K_f(\gamma x, y) = K_f(x,y)$ and $K_f(x, \gamma y) = K_f(x,y)$, where $\gamma$ acts through its adelic image; and for all $a \in \mathbb{A}^{\times}$ and all $x,y$ one has $K_f(a x, y) = \xi(a) K_f(x,y)$ and $K_f(x, a y) = \xi(a)^{-1} K_f(x,y)$, with $a$ acting by the scalar matrix $\mathrm{diag}(a,a)$.
--
--   This is the regularity and invariance statement for the centre-folded automorphic kernel attached to a test function $f$ on $\mathrm{GL}_2(\mathbb{A})$ and a central character $\xi$, the kernel representing the convolution operator on automorphic forms with central character $\xi$ in the Arthur–Selberg setting. It is used by the statements establishing the pointwise and truncated spectral expansions of that kernel, where joint continuity and the two-sided $\mathrm{GL}_2(K)$-invariance and central equivariance allow the kernel to be regarded as a function on the relevant quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    (Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * p.2)) ∂νZK) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f ((AutomorphicForm.globalPoints (𝓞 K) K γ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK) =
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK)) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * (AutomorphicForm.globalPoints (𝓞 K) K γ * y))) ∂νZK) =
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK)) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f ((AutomorphicForm.centralScalar (𝓞 K) K a * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) *
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK)) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * (AutomorphicForm.centralScalar (𝓞 K) K a * y))) ∂νZK) =
      (((ξK ⟨a, Subgroup.mem_top a⟩)⁻¹ : ℂˣ) : ℂ) *
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK)) := by sorry
