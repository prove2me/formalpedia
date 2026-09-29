-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
-- name    : AutomorphicForm.convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/d23e6e0f-2098-581d-9733-9a7a4c28826e
-- title:
--   Right convolution preserves level, type cut and K_∞-finiteness
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the unit group of the adele ring $\mathbb{A}_K$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function of the idele $z$, trivial on the image of $K^\times$ under the map induced by $K \to \mathbb{A}_K$, and of absolute value $1$ at every idele. Let $N$ be a nonzero ideal of $\mathcal{O}_K$, write $U(N)$ for the intersection of `principalLevel` $(\mathcal{O}_K,K,N)$, i.e. of `levelOne` at $N$ with its conjugate by the Weyl element, with `finiteAdelicGL2Subgroup` $K$ (the kernel of the archimedean projection `glArch`), and let $\mathcal{T}$ be an `ArchTypeFamily` for $K$, that is a number `card` $w$ of archimedean types `rep` $w$ at each infinite place $w$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support, left invariant under $U(N)$, and invariant under conjugation by $\mathrm{rowIsometryInclAt₀}$ of every element of $\mathrm{rowIsometrySubgroup₀}$ at every infinite place. Let $v : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt` for $\xi_K$ with respect to the production pins built from the truncation domain `canonicalTruncationDomain` $K\,\alpha\,\beta$, the level subgroups $M \mapsto U(M)$, the Hecke generators `heckeGen`, the box `adelicBox` $K$, the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ and the conditional additive Haar measure on the box, and assume in addition that $v$ is right $U(N)$-invariant and lies in `archCutSubmodule` $K\,\mathcal{T}$, the intersection over infinite places $w$ of the sum of the type submodules $\mathrm{archTypeSubmoduleAt}\,w\,(\mathcal{T}.\mathrm{rep}\,w\,i)$. Then the right convolution $\mathrm{convOp}\,K\,f\,v = \mathrm{rightConv}\,K\,v\,f$ is again right $U(N)$-invariant, lies in `archCutSubmodule` $K\,\mathcal{T}$, and is `IsArchKFinite`, i.e. at every infinite place $w$ its translates under the archimedean row-isometry subgroup at $w$ span a finite-dimensional space.
--
--   This is the regularity step for smoothing by convolution: convolving an automorphic function against a compactly supported test function that is left invariant under the level group and conjugation-invariant under the archimedean row isometries retains the level-$N$ right invariance and the prescribed archimedean types, and produces a $K_\infty$-finite function. It feeds the approximation statement [`AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt`](thm.html#AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt), where automorphic functions are approximated in $L^2$ by continuous, $K_\infty$-finite ones of the same level and type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfN : ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ y : AdelicGL2 (𝓞 K) K, f (u * y) = f y)
    (_hfK : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
      f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y)
    (v : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (_hvN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g)
    (_hvt : v ∈ archCutSubmodule K tysK) :
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        convOp K f v (g * u') = convOp K f v g) ∧
      convOp K f v ∈ archCutSubmodule K tysK ∧
      IsArchKFinite K (convOp K f v) := by sorry
