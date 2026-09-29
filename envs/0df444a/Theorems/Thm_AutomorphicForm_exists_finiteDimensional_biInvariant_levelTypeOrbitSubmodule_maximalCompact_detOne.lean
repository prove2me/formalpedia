-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
-- name    : AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/10495aca-0cdb-5ab9-b775-e52eb33e92ff
-- title:
--   Finite-dimensional level–type orbit space on the maximal compact
-- statement:
--   Let $K$ be a number field, let $\xi_K$ be a homomorphism from the full subgroup of units of the adele ring of $K$ to $\mathbb{C}^\times$ whose values all have absolute value $1$, let $N$ be a nonzero ideal of $\mathcal{O}_K$, and let $\mathrm{tys}_K$ be an `ArchTypeFamily` for $K$, i.e. a number $\mathrm{card}(w)$ of types at each infinite place $w$ together with, for each index, a finite-dimensional complex representation of `rowIsometrySubgroup₀` of $K_w$. Write $\mathbf{K} =$ `adelicMaximalCompact K` for the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of those $k$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ satisfies `IsRowIsometry` (unit determinant norm and preservation of $\|x\|^2+\|y\|^2$ under the row pairing), and write $\mathbf{K}'$ for the elements of $\mathbf{K}$ whose archimedean component at every real place has determinant exactly $1$; write $U =$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the intersection of the level-$N$ principal subgroup (`levelOne` at $N$ intersected with its conjugate by the Weyl element) with the kernel of `glArch`. Then there is a complex subspace $E$ of the space of functions $\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that: $E$ is finite-dimensional; every $v \in E$ is continuous on $\mathbf{K}$; every $v \in E$ vanishes off $\mathbf{K}'$; $E$ is stable under left and right translation by elements of $\mathbf{K}'$; $E$ is stable under $v \mapsto \overline{v(\,\cdot^{-1})}$; for each $v \in E$ there is a finite set of functions continuous on $\mathbf{K}$ whose span contains all left translates $x \mapsto v(kx)$ with $k \in \mathbf{K}$; every $v \in E$ is right $U$-invariant; $E \le$ `archCutSubmodule K tysK`, the intersection over infinite places $w$ of the sum over $i < \mathrm{card}(w)$ of the type submodules attached to $\mathrm{tys}_K$; and, finally, for every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ that is `IsArchKFinite` (at each infinite place its right translates under the archimedean row-isometry subgroup span a finite-dimensional space), is right $U$-invariant, lies in `archCutSubmodule K tysK`, and transforms under the central scalars by $\xi_K$ in the sense that $\varphi(g \cdot zI) = \xi_K(z)\varphi(g)$ for all ideles $z$ and all $g$, and for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$, there is $v \in E$ with $v(k) = \varphi(xk)$ for all $k \in \mathbf{K}'$.
--
--   This is the representation-theoretic core of the level–type averaging construction: it produces a single finite-dimensional, bi-$\mathbf{K}'$-stable and $*$-stable space of functions on the maximal compact subgroup that captures the $\mathbf{K}'$-orbit of every continuous, $K_\infty$-finite, level-$N$, typed function with central character $\xi_K$. It is used by the two constructions of a continuous idempotent averaging kernel on the maximal compact which commutes with the row-isometry subgroups and fixes such functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne.lean

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

theorem AutomorphicForm.exists_finiteDimensional_biInvariant_levelTypeOrbitSubmodule_maximalCompact_detOne
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ E ∧
      (∀ v ∈ E, Continuous fun k : ↥(adelicMaximalCompact K) => v (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 K) K, v x ≠ 0 → x ∈ adelicMaximalCompact K ∧ (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K x) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1)) ∧
      (∀ k ∈ adelicMaximalCompact K, (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ v ∈ E, (fun x => v (k * x)) ∈ E ∧ (fun x => v (x * k)) ∈ E) ∧
      (∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ E) ∧
      (∀ v ∈ E, ∃ S : Finset (AdelicGL2 (𝓞 K) K → ℂ),
        (∀ s ∈ S, Continuous fun k : ↥(adelicMaximalCompact K) => s (k : AdelicGL2 (𝓞 K) K)) ∧
        ∀ k ∈ adelicMaximalCompact K,
          (fun x => v (k * x)) ∈ Submodule.span ℂ (S : Set (AdelicGL2 (𝓞 K) K → ℂ))) ∧
      (∀ v ∈ E, ∀ (x : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        v (x * u) = v x) ∧
      E ≤ archCutSubmodule K tysK ∧
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        ∀ x : AdelicGL2 (𝓞 K) K, ∃ v ∈ E, ∀ k ∈ adelicMaximalCompact K, (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K k) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
          v k = φ (x * k)) := by sorry
