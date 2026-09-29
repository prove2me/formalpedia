-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule_of_continuous
-- name    : AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/09ecac5e-f03c-5d97-ac64-236fb07c7a01
-- title:
--   Level–type averaging kernel on the adelic maximal compact
-- statement:
--   Let $K$ be a number field, let $\xi_K$ be a homomorphism from the full unit group of the adele ring $\mathbb{A}_K$ (as the top subgroup) to $\mathbb{C}^\times$ all of whose values have absolute value $1$, let $N \neq 0$ be an ideal of $\mathcal{O}_K$, and let $\mathcal{T}$ be an archimedean type family, i.e. a number $\mathrm{card}(w)$ of finite-dimensional representations $\rho$ of the row-isometry group at each infinite place $w$. Write $\mathbf{K} =$ `adelicMaximalCompact K` for the subgroup of $g \in \mathrm{GL}_2(\mathbb{A}_K)$ whose finite part is integral and whose component at every infinite place $w$ is a row isometry (determinant of norm $1$, and the two rows acting isometrically for the sum-of-squares norm on $w$-completion pairs), equipped with the Haar measure `maximalCompactHaar K`. Then there exists a continuous $\kappa : \mathbf{K} \to \mathbb{C}$ with $\kappa(k^{-1}) = \overline{\kappa(k)}$ and $\int_{\mathbf{K}} \kappa(k')\kappa(k'^{-1}k)\,dk' = \kappa(k)$ for all $k$, such that, writing $(P\varphi)(g) = \int_{\mathbf{K}} \kappa(k)\varphi(gk)\,dk$: (o) for every function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_K)$, with no regularity assumed, and every $k_0 \in \mathbf{K}$ whose archimedean component has determinant exactly $1$ at every real place, $\int \kappa(k)\varphi(g k k_0)\,dk = \int \kappa(k)\varphi(g k_0 k)\,dk$ for all $g$; (i) $P\varphi = \varphi$ for every continuous $\varphi$ that is archimedean $K$-finite (at each infinite place the right translates under the archimedean row-isometry subgroup span a finite-dimensional space), is right invariant under the finite elements of the principal level $N$ subgroup (the intersection of `principalLevel (𝓞 K) K N` with the kernel of the archimedean projection), lies in the archimedean cut submodule $\bigsqcap_w \bigsqcup_i$ of the type submodules attached to $\mathcal{T}$, and transforms under the central scalars $z$ by $\xi_K(z)$; (ii) for every continuous $\varphi$, $P\varphi$ is continuous, archimedean $K$-finite, right invariant under those finite level-$N$ elements, and lies in the archimedean cut submodule; and (iii) $P(P\varphi) = P\varphi$ for every continuous $\varphi$.
--
--   This produces the self-adjoint convolution idempotent on the adelic maximal compact subgroup which projects continuous functions onto the space of functions of prescribed level $N$ and prescribed archimedean $K$-types, the adelic analogue of projection against a matrix coefficient of a finite sum of $K$-types. Clauses (ii) and (iii) are stated for arbitrary continuous functions rather than only $K$-finite ones, which is what the construction of level-$N$, type-$\mathcal{T}$ automorphic forms from Paley–Wiener wave packets requires, and it is that construction which cites this result.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule_of_continuous.lean

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
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule_of_continuous
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ κ : ↥(adelicMaximalCompact K) → ℂ, Continuous κ ∧ (∀ k, κ k⁻¹ = conj (κ k)) ∧
      (∀ k : ↥(adelicMaximalCompact K), ∫ k', κ k' * κ (k'⁻¹ * k) ∂(maximalCompactHaar K) = κ k) ∧

      (∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K,
          (∫ k', κ k' * φ (g * (k' : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
            ∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ → (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = φ) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ →
        Continuous (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        IsArchKFinite K (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) (g * u) = (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) g) ∧
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∈ archCutSubmodule K tysK) ∧

      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ →
        (fun g => ∫ k, κ k * (∫ k', κ k' * φ (g * (k : AdelicGL2 (𝓞 K) K) * (k' : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
          ∂(maximalCompactHaar K)) =
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by sorry
