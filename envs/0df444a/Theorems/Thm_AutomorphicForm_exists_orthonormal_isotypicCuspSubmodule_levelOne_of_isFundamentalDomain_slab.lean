-- Prove2me | Theorems.Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/1d5c2caa-c4f3-5658-b617-352dd1a54dd2
-- title:
--   Orthonormal complete cusp system at level N on a slab
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be contained in the slab $\{g:\ \lVert\det g\rVert\in[\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the idele norm given by the distributive Haar character, and let $\Phi$ be a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ on that slab, with respect to the Haar measure `adelicGLHaar` restricted to the slab. Fix a homomorphism $\xi$ from the full unit group of $\mathbb{A}_K$ to $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_K$, a finite set $S$ of finite places containing every prime divisor of $N$, and an archimedean type family `tys` (for each infinite place $w$ a number $\mathrm{card}\,w$ and that many archimedean types at $w$). Write $\mathcal{P}$ for the carrier pins assembled from $\Phi$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\text{archimedean projection})$, the Hecke generators `heckeGen` at the finite places, central subgroup $\top$, and the conditional measure on the adelic box. Then there are an index type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$ such that: each $\mathrm{cls}(i)$ lies in `cuspClasses` for $\mathcal{P},\xi,N,S$ (level $N$, vanishing $a_v,b_v$ for $v\in S$, nonzero isotypic cusp submodule) and $b_i$ lies in the isotypic cusp submodule for $\mathrm{cls}(i)$ intersected with the archimedean cut submodule $\mathrm{archCut}(\mathrm{tys})$; the $b_i$ are orthonormal for the pairing $\int_\Phi b_i\overline{b_j}\,d\mu$; for every cusp class $\pi$ the fibre $\{i:\mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ equals the isotypic cusp submodule at $\pi$ intersected with $\mathrm{archCut}(\mathrm{tys})$; and the system is complete, in that any $\varphi$ which is a smooth cusp automorphic function at $\mathcal{P}$ with character $\xi$, is continuous, is right invariant under $\mathcal{P}.U\,N$, lies in $\mathrm{archCut}(\mathrm{tys})$ and satisfies $\int_\Phi \varphi\,\overline{b_i}=0$ for all $i$, vanishes almost everywhere on $\Phi$.
--
--   This is the discreteness and orthogonal decomposition of the cuspidal spectrum of $\mathrm{GL}_2$ over a number field, in the concrete form of an orthonormal family of cusp forms on a fundamental domain for a determinant slab, indexed by Hecke eigensystems of level $N$ and adapted to a prescribed finite set of archimedean types. It serves as the spectral input for the trace-formula computations, being used in the convergence and summability statements for convolution and twisted convolution operators and in the atomic limit formula for twisted cut traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_orthonormal_isotypicCuspSubmodule_levelOne_of_isFundamentalDomain_slab
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
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S ∧
        b i ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys) ∧
      (∀ i, ∫ g in Φ, b i g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) ∧
      (∀ i j, i ≠ j → ∫ g in Φ, b i g * starRingEnd ℂ (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) ∧
      (∀ π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys) ∧
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
        IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ φ →
        Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tys →
        (∀ i, ∫ g in Φ, φ g * starRingEnd ℂ (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0) := by sorry
