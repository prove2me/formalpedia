-- Prove2me | Theorems.Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
-- name    : AutomorphicForm.le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/15603afc-1acd-5d62-92a6-665507f4e93d
-- title:
--   Finite-dimensional Hecke-stable cusp spaces lie in isotypic sums
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be contained in the slab $\{g:\lVert\det g\rVert\in[\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the module of the idèle (`ideleNorm`, the distinguished Haar character), and be a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` with respect to the Haar measure `adelicGLHaar` restricted to that slab. Fix a homomorphism $\xi$ from the full idèle unit group to $\mathbb{C}^\times$, a nonzero ideal $N\subseteq\mathcal{O}_K$, a finite set $S$ of finite places containing every $w$ with $w\mid N$, and an archimedean type family `tys` (for each infinite place $w$, finitely many representations of `rowIsometrySubgroup₀`). Write `pins` for the carrier data `productionPinsOf` assembled from $\Phi$, the levels $U(M)=\mathrm{principalLevel}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}(v)$, central subgroup $\top$, Borel structures, and the additive adelic Haar measure conditioned on `adelicBox`. Let $X$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ each of whose elements $x$ is a smooth cuspidal automorphic function at `pins` with character $\xi$ (cuspidal automorphic, and smooth for the finite-adelic subgroup), is continuous, satisfies $x(gu)=x(g)$ for all $u\in U(N)$, and lies in $\mathrm{archCutSubmodule}$ of `tys`, namely the intersection over infinite places $w$ of the span of the listed archimedean type subspaces at $w$. Assume $X$ is finite-dimensional over $\mathbb{C}$, and that for every $v\notin S$ and every family $\mathrm{reps}:\mathrm{Fin}(|\mathcal{O}_K/v|+1)\to\mathrm{GL}_2(\mathbb{A}_K)$ which is a Hecke coset system for $U(N)$ and $\mathrm{heckeGen}(v)$ (each representative lies in the double coset, the representatives cover it modulo $U(N)$ on the right, and the induced cosets are distinct), the function $g\mapsto\sum_i x(g\,\mathrm{reps}\,i)$ lies in $X$ whenever $x\in X$. Then $X$ is contained in the supremum, over Hecke eigensystems $\pi$ of level $N$ whose $a$- and $b$-values vanish on $S$ and whose isotypic cuspidal submodule is nonzero, of the intersection of $\mathrm{isotypicCuspSubmodule}$ at $(\textsf{pins},\xi,N,S,\pi)$ — the span of the continuous, $U(N)$-right-invariant smooth cuspidal automorphic functions that are Hecke coset eigenfunctions with eigenvalue $\pi.a(v)$ and central eigenfunctions with eigenvalue $\pi.b(v)$ at every $v\notin S$ — with $\mathrm{archCutSubmodule}$ of `tys`.
--
--   This is the simultaneous diagonalisation of the unramified Hecke operators on a finite-dimensional Hecke-stable space of $\mathrm{GL}_2$ cusp forms of principal congruence level $N$ with prescribed archimedean types: such a space is exhausted by the isotypic pieces of the cuspidal eigensystems of level $N$, cut by the archimedean type condition. It feeds the construction of an orthonormal family inside these isotypic spaces over a slab fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
AutomorphicForm.le_iSup_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
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
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ x ∧
        Continuous x ∧
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
          (productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N,
          x (g * u) = x g) ∧
        x ∈ archCutSubmodule K tys)
    (hfin : FiniteDimensional ℂ X)
    (hstab : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K,
        HeckeIntegralSeam.IsHeckeCosetSystem
          ((productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).U N)
          ((productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).gen v) reps →
        ∀ x ∈ X, SmoothCusp.heckeCosetSum K reps x ∈ X) :
    X ≤ ⨆ (π : HeckeEigensystem K ℂ) (_ : π ∈ cuspClasses K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S),
        isotypicCuspSubmodule K
          (productionPinsOf K Φ
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys := by sorry
