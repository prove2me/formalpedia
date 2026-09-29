-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- name    : AutomorphicForm.setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/dc0c4887-e92b-5fdf-83e1-faa0436c6dac
-- title:
--   Vanishing of the hyperbolic ξ-fold for a ramified central character
-- statement:
--   Let $K$ be a number field, $\Phi_K$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (where $\mathbb{A}_K$ is the adele ring of $K$), and fix a Borel measurable structure on the idele units $\mathbb{A}_K^\times$ together with a Haar measure $\nu_{Z_K}$. Let $\Omega_K \subseteq \mathbb{A}_K^\times$ be a fundamental domain, in the sense of `IsFundamentalDomain` for $\nu_{Z_K}$, for the range of the map $K^\times \to \mathbb{A}_K^\times$ induced by $K \to \mathbb{A}_K$, and let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is trivial on that range, so an idele class character. Let $\varphi_K : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, let $z_0 \in \mathbb{A}_K^\times$ satisfy $\xi(z_0) \neq 1$, and assume $\varphi_K(g\,c(z_0)) = \varphi_K(g)$ for all $g$, where $c(z) = \mathrm{scalar}(z)$ is the central scalar matrix with entries $z$. Then for every real $R$ and every $x \in \mathrm{GL}_2(\mathbb{A}_K)$, the integral over $\Omega_K$ against $\nu_{Z_K}$ of $\xi(z)$ times the difference of (i) the hyperbolic part $\sum_{\gamma \in \mathrm{hyperbolicCell}\,K}^{\mathrm{f}} \varphi_K(x^{-1}\gamma\,c(z)x)$ of the adelic kernel, the finite-support sum over the set `hyperbolicCell` of $\mathrm{GL}_2(K)$, and (ii) the value at $c(z)x$ of the indicator of $\{g : \exp R < \mathrm{adelicHeight}_K(g)\}$ times the constant term along the unipotent family $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$, integrated against the measure attached to `productionPinsOf` for the data $(\Phi_K,\ M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup},\ v \mapsto \mathrm{heckeGen}(v),\ \mathrm{adelicBox}\,K)$, namely the adelic additive Haar measure conditioned on $\mathrm{adelicBox}\,K$, of the function $y \mapsto \sum^{\mathrm{f}}_{\gamma} \varphi_K(x^{-1}\gamma y)$ over those $\gamma \in \mathrm{GL}_2(K)$ with $\gamma_{10} = 0$ and $\gamma_{00}/\gamma_{11} \neq 1$, equals $0$.
--
--   This is the standard vanishing of a $\xi$-weighted central integral in the trace formula: when the idele class character is non-trivial on a central idele under which the test function is invariant, translating the central variable leaves the integrand unchanged while multiplying it by $\xi(z_0) \neq 1$, so the truncated hyperbolic contribution dies. It is the hyperbolic-cell counterpart of the same statement for the unipotent cell, and is used in the assembly of the hyperbolic term ([`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine)) to dispose of the ramified case with trivial winding data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one.lean

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

theorem AutomorphicForm.setIntegral_hyperbolicCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
    (K : Type) [Field K] [NumberField K]
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
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
    (R : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    (AutomorphicForm.adelicKernelHyperbolicPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
      (@AutomorphicForm.constantTerm _
        (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
        (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
          (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
            (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
          φK (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) = 0 := by sorry
