-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt
-- name    : AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9d6ed5f9-cdce-5878-b2d4-816300786322
-- title:
--   L²-density of continuous K_∞-finite automorphic functions
-- statement:
--   Let $K$ be a number field (with decidable equality on the height one spectrum of $\mathcal O_K$), let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb A_K)^\times$ to $\mathbb C^\times$ which is continuous as a $\mathbb C$-valued function, trivial on the image of $K^\times$ under `Units.map` of the structure map $K \to \mathbb A_K$, and of absolute value $1$ everywhere. Fix a nonzero ideal $N$ of $\mathcal O_K$, a family `tysK : ArchTypeFamily K` assigning to each infinite place $w$ a number `card w` of archimedean representations `rep w i`, and a function $v$ on $\mathrm{GL}_2(\mathbb A_K)$ with values in $\mathbb C$. Assume $v$ satisfies `IsAutomorphicFnAt` for the carrier pins `productionPinsOf` built from the domain `canonicalTruncationDomain K α β`, the level groups $M \mapsto$ `principalLevel` $(\mathcal O_K,K,M)$ intersected with `finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen`, and the box `adelicBox K` (so: the Borel structure `glBorel`, the Haar measure `adelicGLHaar`, central subgroup $\top$, and on the adeles the Borel structure and the additive Haar measure conditioned on `adelicBox K`), with character $\xi_K$; assume further that $v(gu')=v(g)$ for all $g$ and all $u'$ in `principalLevel` $(\mathcal O_K,K,N)\ \sqcap$ `finiteAdelicGL2Subgroup K`, and that $v$ lies in `archCutSubmodule K tysK`, the infimum over infinite places $w$ of the supremum over $i <$ `card w` of the submodules `archTypeSubmoduleAt K w (tysK.rep w i)`. Then for every $\varepsilon>0$ there exists $w$ enjoying all the same properties — the same `IsAutomorphicFnAt` condition, right invariance under `principalLevel` $(\mathcal O_K,K,N)\ \sqcap$ `finiteAdelicGL2Subgroup K`, and membership in `archCutSubmodule K tysK` — and in addition continuous and `IsArchKFinite`, i.e. for each infinite place the right translates of $w$ under `archRowIsometrySubgroup K w` span a finite-dimensional space, such that the $L^2$ norm `eLpNorm (v - w) 2` with respect to `adelicGLHaar` restricted to `canonicalTruncationDomain K α β` is less than `ENNReal.ofReal ε`.
--
--   This is the density statement that continuous, archimedean $K$-finite, right level-$N$-invariant functions of prescribed archimedean types are $L^2$-dense, on the canonical truncation domain, in the automorphic functions with those invariance properties but no regularity assumption. It is used in the proof that the level-and-type averaging operator fixes such automorphic functions almost everywhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt.lean

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

theorem AutomorphicForm.exists_isAutomorphicFnAt_continuous_isArchKFinite_principalLevel_archCutSubmodule_eLpNorm_sub_lt_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (v : AdelicGL2 (𝓞 K) K → ℂ)
    (_hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v)
    (_hvN : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g)
    (_hvt : v ∈ archCutSubmodule K tysK)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w ∧
      Continuous w ∧ IsArchKFinite K w ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, w (g * u') = w g) ∧
      w ∈ archCutSubmodule K tysK ∧
      eLpNorm (v - w) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) <
        ENNReal.ofReal ε := by sorry
