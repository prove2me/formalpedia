-- Prove2me | Theorems.Thm_AutomorphicForm_countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/063332c7-2548-5bb1-ac75-13c49a83191f
-- title:
--   Countable index set for orthonormal adelic cusp forms
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the determinant slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the module of the distinguished Haar character, and assume $\Phi$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ under the diagonal embedding, with respect to the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that slab. Let $\xi$ be a homomorphism from the full unit group $(\mathbb{A}_K)^\times$ (as the subgroup $\top$) to $\mathbb{C}^\times$, let $S$ be a finite set of finite places of $K$, and let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S$. Let `tys` assign to each infinite place $w$ a finite list of archimedean types, each a representation of `rowIsometrySubgroup₀` of the completion at $w$ on a finite-dimensional complex space; `archCutSubmodule` is the intersection over $w$ of the sums of the corresponding type subspaces. Fix a type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ (each consisting of a nonzero level ideal and complex families $a_v,b_v$), all data for the carrier pins `productionPinsOf` built from $\Phi$, the levels $M\mapsto$ `principalLevel` $M$ intersected with the kernel of the archimedean projection, the Hecke generators `heckeGen`, the central subgroup $\top$, and the conditional adelic measure on the box `adelicBox`. Assume: each $\mathrm{cls}(i)$ lies in `cuspClasses` (level exactly $N$, vanishing $a_v$ and $b_v$ for $v\in S$, and nonzero isotypic cuspidal subspace) and $b_i$ lies in the $\mathrm{cls}(i)$-isotypic cuspidal submodule intersected with `archCutSubmodule`; the family is orthonormal, $\int_\Phi b_i\overline{b_i}=1$ and $\int_\Phi b_i\overline{b_j}=0$ for $i\neq j$ against `adelicGLHaar`; and for every class $\pi$ in `cuspClasses` the set of indices $i$ with $\mathrm{cls}(i)=\pi$ is finite and the $b_i$ over it span the corresponding cut isotypic subspace. Then $\iota$ is countable.
--
--   A finiteness-of-multiplicity statement of the classical discreteness theory of the cuspidal spectrum: an orthonormal system of adelic cusp forms of fixed level, central character and archimedean types has at most countably many members. It feeds the convergence and integrability arguments for sums over such an orthonormal basis, being cited in the integrability statement for the spectral sum of convolution operators twisted by unipotent translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.countable_index_of_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0)
    (hbs : ∀ π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys) :
    Countable ι := by sorry
