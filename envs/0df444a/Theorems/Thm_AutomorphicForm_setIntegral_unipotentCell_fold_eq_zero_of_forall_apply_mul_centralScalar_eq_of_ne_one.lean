-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_unipotentCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- name    : AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/da80129b-64a4-5cc7-a3ba-ae6482d3255f
-- title:
--   Vanishing of the ξ-twisted unipotent fold under central invariance
-- statement:
--   Let $K$ be a number field, $\Phi_K$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and let the unit group $\mathbb{A}_K^\times$ carry a Borel measurable structure and a Haar measure $\nu_{Z_K}$. Let $\Omega_K \subseteq \mathbb{A}_K^\times$ be a fundamental domain, in the sense of `IsFundamentalDomain` for $\nu_{Z_K}$, for the image of $K^\times$ under the map induced on units by $K \to \mathbb{A}_K$. Let $\xi$ be a homomorphism from the full subgroup $\top \le \mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is trivial on that image of $K^\times$, let $\varphi_K : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, and let $z_0 \in \mathbb{A}_K^\times$ satisfy $\xi(z_0) \neq 1$ together with $\varphi_K(g \cdot \mathrm{diag}(z_0,z_0)) = \varphi_K(g)$ for every $g$, where $\mathrm{diag}$ denotes `centralScalar`, the scalar embedding $\mathbb{A}_K^\times \to \mathrm{GL}_2(\mathbb{A}_K)$. Then for every real $R$ and every $x \in \mathrm{GL}_2(\mathbb{A}_K)$ the integral over $z \in \Omega_K$, against $\nu_{Z_K}$, of $\xi(z)$ times the difference of (i) the unipotent fold $\sum^{\mathrm{f}}_{\gamma \in \mathrm{unipotentCell}\,K} \varphi_K(x^{-1} \gamma_{\mathbb{A}} (\mathrm{diag}(z,z)x))$, $\gamma \mapsto \gamma_{\mathbb{A}}$ being `globalPoints`, and (ii) the value at $\mathrm{diag}(z,z)x$ of the indicator, on the set where `adelicHeight` $K$ exceeds $e^R$, of the constant term `constantTerm` formed from the one-parameter unipotent family $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$, the function $y \mapsto \sum^{\mathrm{f}}_{\gamma} \varphi_K(x^{-1}\gamma_{\mathbb{A}} y)$ summed over those $\gamma \in \mathrm{GL}_2(K)$ with lower-left entry $0$ and ratio of diagonal entries $1$, and the measure on $\mathbb{A}_K$ supplied by `productionPinsOf`, namely the additive adelic Haar measure conditioned on `adelicBox` $K$, equals $0$. The data $\Phi_K$, the level subgroups $M \mapsto$ `principalLevel` $\sqcap$ `finiteAdelicGL2Subgroup`, and the Hecke generators `heckeGen` enter only as further fields of that record and do not affect the measure used.
--
--   This is the central-character obstruction for the unipotent cell in the adelic $\mathrm{GL}_2$ trace-formula computation with Siegel truncation: a test function invariant under a central idele on which $\xi$ is non-trivial makes the $\xi$-twisted unipotent contribution, truncated by the adelic height, vanish. It is the unipotent-cell companion of the corresponding statement for the geometric remainder, and it is used in [`AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one`](thm.html#AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one), where the non-trivial central element is produced locally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_unipotentCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one.lean

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

theorem AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_forall_apply_mul_centralScalar_eq_of_ne_one
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
    (AutomorphicForm.adelicKernelUnipotentPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
      (@AutomorphicForm.constantTerm _
        (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
        (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
          (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
            (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
          φK (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
      (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) = 0 := by sorry
