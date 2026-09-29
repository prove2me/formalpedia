-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
-- name    : AutomorphicForm.exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e2e9d682-dd7b-5dd4-85d8-7fa4546bc265
-- title:
--   Uniform weight bound for non-zero induced sections of listed type
-- statement:
--   Let $K$ be a number field and let $\xi_K$ be a homomorphism from the full group of idele units of $K$ to $\mathbb{C}^\times$ which is continuous, trivial on the image of $K^\times$, and of modulus $\|z\|^{w}$ for a fixed real $w$, where $\|\cdot\|$ denotes the idele norm given by the module character `distribHaarChar` of the adele ring; let $N$ be an ideal of $\mathcal{O}_K$ and $\mathcal{T}$ an `ArchTypeFamily`, that is, for each infinite place $v$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_v)$ on spaces $\mathbb{C}^{n}$. Write $\alpha$ for the positive real-valued character of the ideles obtained from `distribHaarChar`. The assertion is the existence of a natural number $M_0$, depending only on these data, such that the following holds for every choice of the subsequent data: a proof that $\alpha$ is positive; continuous homomorphisms $\mu,\nu$ from the idele units to $\mathbb{C}^\times$ which are unitary ($|\mu(x)|=|\nu(x)|=1$ everywhere), trivial on $K^\times$, and satisfy $\mu(z)\nu(z)\|z\|^{w}=\xi_K(z)$; a function $\varphi$ on adelic $\mathrm{GL}_2$ transforming under the Borel subgroup (lower-left entry zero) by $\varphi(bg)=\mu\alpha^{1/2}(b_{11})\,\nu\alpha^{-1/2}(b_{22})\,\varphi(g)$, continuous, with finitely spanned right translates under each archimedean row-isometry subgroup, with open stabiliser under right translation by the kernel of the archimedean projection, such that for each infinite place the functions $k\mapsto\varphi(gk)$ on the archimedean row-isometry subgroup all lie in one finite-dimensional complex subspace, invariant under right translation by the intersection of the principal level subgroup of $N$ with that kernel, lying in the cut submodule attached to $\mathcal{T}$ (at every infinite place, in the sum of the type submodules listed there), and non-zero; and integers $m^\mu_v,m^\nu_v$ such that the local archimedean components of $\mu$ and $\nu$ at $v$ send each norm-one unit $x$ of $K_v$ to $x^{m^\mu_v}$, respectively $x^{m^\nu_v}$, with $m^\mu_v,m^\nu_v\in\{0,1\}$ at real places. Then $|m^\mu_v|\le M_0$ and $|m^\nu_v|\le M_0$ for every infinite place $v$.
--
--   This is the archimedean weight bound for principal-series sections of prescribed $K$-type: prescribing finitely many types at the infinite places and requiring a non-zero section of the induced representation $I(\mu\alpha^{1/2},\nu\alpha^{-1/2})$ bounds the integer weights of the local components of $\mu$ and $\nu$ uniformly in the pair $(\mu,\nu)$. It feeds the finiteness and summability statements for orthonormal families of flat induced sections of given level and type, and the decomposition of flat restrictions over same-class data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem AutomorphicForm.exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ M₀ : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm 0) (etaSnd ν αm hαm 0) φ)
      (_hφK : IsArchKFinite K φ) (_hφf : IsKfSmooth K φ) (_hφc : Continuous φ)
      (_hφKu : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
          (fun k : ↥(archRowIsometrySubgroup K w) => φ (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (_hφty : φ ∈ archCutSubmodule K tysK)
      (_hφ0 : φ ≠ 0)
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (_hreal : ∀ v : InfinitePlace K, v.IsReal → (mμ v = 0 ∨ mμ v = 1) ∧ (mν v = 0 ∨ mν v = 1)),
      ∀ v : InfinitePlace K, |mμ v| ≤ (M₀ : ℤ) ∧ |mν v| ≤ (M₀ : ℤ) := by sorry
