-- Prove2me | Theorems.Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
-- name    : AutomorphicForm.le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/25bcafd5-d769-57d4-8727-05ff2a8bf26a
-- title:
--   Finite-dimensional Hecke-stable cusp space lies in isotypic cut subspaces
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the slab $\{g : \lVert\det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the idele norm given by the module of the distributive Haar character, and assume $\Phi$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that slab. Let $\xi$ be a homomorphism from the full unit group of $\mathbb{A}_K$ to $\mathbb{C}^\times$, let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $S$ be a finite set of finite places containing every $w$ with $w \mid N$, and let `tys` be an archimedean type family, assigning to each infinite place $w$ finitely many representations of the group `rowIsometrySubgroup₀` of its completion. Work with the carrier data `productionPinsOf` built from $\Phi$, from the level groups $U(M)=$ `levelOne` $(M)$ intersected with the finite-adelic subgroup (the kernel of the archimedean projection), from the standard Hecke generators `heckeGen` at the finite places, and from the adelic box, whose central subgroup is all of $\mathbb{A}_K^\times$ and whose cuspidality measure is the adelic additive Haar measure conditioned on the box. Let $X$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ such that every $x\in X$ is automorphic at these data with character $\xi$ and cuspidal along the unipotent subgroup, a smooth vector for right translation by the finite-adelic subgroup, continuous, right invariant under $U(N)$, and lies in `archCutSubmodule K tys`, the intersection over infinite places $w$ of the sums of the type submodules attached to the given representations at $w$. Assume $X$ is finite-dimensional over $\mathbb{C}$, and that for every finite place $v\notin S$ and every family $reps$ indexed by $\mathrm{Fin}(\mathrm{absNorm}(v)+1)$ which is a Hecke coset system for $U(N)$ and `heckeGen` $v$ (each $reps_i$ lies in the double coset, the $reps_i$ meet every coset of the double coset modulo $U(N)$, and their classes in $\mathrm{GL}_2(\mathbb{A}_K)/U(N)$ are distinct), the operator $x\mapsto (g\mapsto \sum_i x(g\,reps_i))$ maps $X$ into $X$. Then $X$ is contained in the supremum, over those Hecke eigensystems $\pi$ for $K$ with complex values whose level is $N$, whose entries $a_v,b_v$ vanish for $v\in S$ and whose isotypic cusp submodule is nonzero, of `isotypicCuspSubmodule K pins ξ N S π` intersected with `archCutSubmodule K tys`.
--
--   This is the finiteness step in the adelic theory of $\mathrm{GL}_2$ cusp forms: a finite-dimensional space of cusp forms of fixed level and fixed archimedean types that is stable under all the Hecke coset operators outside $S$ decomposes into the isotypic pieces of the cuspidal Hecke eigensystems. It is used to express twisted cut traces as finite sums over eigensystems and to produce orthonormal bases of the isotypic cuspidal spaces of level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
AutomorphicForm.le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K) (X : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hX : ∀ x ∈ X,
      IsSmoothCuspAutomorphicFnAt K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ x ∧
        Continuous x ∧
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N,
          x (g * u) = x g) ∧
        x ∈ archCutSubmodule K tys)
    (hfin : FiniteDimensional ℂ X)
    (hstab : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem
          ((productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N)
          ((productionPinsOf K Φ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).gen v) reps →
        ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X) :
    X ≤ ⨆ (π : HeckeEigensystem K ℂ) (_ : π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S),
        isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys := by sorry
