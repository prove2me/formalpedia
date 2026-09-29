-- Prove2me | Theorems.Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/7ae2f49a-f261-57c6-a923-e4c017a1200f
-- title:
--   Orthonormal Hecke-adapted basis of the cut cuspidal space
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi$ be a subset of $\mathrm{GL}_2$ of the adele ring of $K$ contained in the slab $\{g : \lVert\det g\rVert \in [\alpha,\beta]\}$, where the norm is the module of the idele $\det g$ for the distributive Haar character, and assume $\Phi$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that slab. Fix a homomorphism $\xi$ from the full unit group of the adele ring to $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_K$, a finite set $S$ of finite places containing every $w$ with $w \mid N$, and an archimedean type family `tys` (a cardinality $\mathrm{card}(w)$ and representation types $\mathrm{rep}\,w\,i$ at each infinite place $w$). Write $P$ for the carrier data `productionPinsOf` assembled from $\Phi$, the level subgroups $N \mapsto \mathrm{principalLevel}(N) \sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, the box `adelicBox K`, the Borel structures and Haar measures, with central subgroup $\top$. Then there exist an index type $\iota$, functions $b_i : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ (each consisting of a nonzero level ideal and coefficient functions $a, b$ on the finite places) such that: every $\mathrm{cls}(i)$ lies in `cuspClasses K P ξ N S`, i.e. has level $N$, has $a_v = b_v = 0$ for $v \in S$, and nonzero isotypic cusp submodule; each $b_i$ lies in `isotypicCuspSubmodule K P ξ N S (cls i)` — the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for that eigensystem — intersected with `archCutSubmodule K tys`, the infimum over infinite places $w$ of the supremum of the archimedean type submodules $\mathrm{rep}\,w\,i$; the $b_i$ are orthonormal for the pairing $\int_\Phi b_i \overline{b_j}$ against `adelicGLHaar`; for each $\pi$ in `cuspClasses K P ξ N S` the fibre $\{i : \mathrm{cls}(i) = \pi\}$ is finite and the span of the corresponding $b_i$ is exactly the $\pi$-isotypic cusp submodule cut by `tys`; and the system is complete, in the sense that any $\varphi$ which is a smooth cusp automorphic function for $P$ and $\xi$, is continuous, is right-invariant under $P.U\,N$, lies in `archCutSubmodule K tys`, and is orthogonal to every $b_i$ over $\Phi$, vanishes almost everywhere for the Haar measure restricted to $\Phi$.
--
--   This is the discreteness statement for the cuspidal spectrum of $\mathrm{GL}_2$ over a number field in the form needed later: an orthonormal system on a slab fundamental domain, indexed compatibly with Hecke eigensystems of principal level $N$, with finite multiplicities, spanning each isotypic piece cut by a prescribed family of archimedean types, and complete in the space of such cusp forms. It is the input to the subsequent spectral expansions and trace-type identities for twisted convolution operators on this space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K) :
    ∃ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S ∧
        b i ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys) ∧
      (∀ i, ∫ g in Φ, b i g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) ∧
      (∀ i j, i ≠ j → ∫ g in Φ, b i g * starRingEnd ℂ (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) ∧
      (∀ π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys) ∧
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
        IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ φ →
        Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tys →
        (∀ i, ∫ g in Φ, φ g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0) := by sorry
