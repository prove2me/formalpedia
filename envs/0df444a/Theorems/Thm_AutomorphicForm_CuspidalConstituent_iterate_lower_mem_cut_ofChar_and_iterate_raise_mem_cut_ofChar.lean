-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
-- name    : AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/5693748b-6e0f-5044-98bf-4566b01d767c
-- title:
--   Iterated lowering and raising operators shift the archimedean weight by two
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the set $D=\bigcup_{x\in T}\{g x: g\in\text{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$ satisfies `CoversModCentre`: every $g$ can be written, after left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar, as an element of $D$. Write `pins` for the carrier data `productionPinsOf` attached to $D$, the level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke elements $v\mapsto \mathrm{heckeGen}\,v$, and the adelic box; its central subgroup is all of $(\mathbb{A}_K)^\times$, and $\xi$ is a character of it. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is a cuspidal constituent for these data and $\xi$: it lies in the $K_\infty$-finite cuspidal submodule, is stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at the infinite places and under right convolution with archimedean-bi-finite factorisable test functions, is non-zero, and contains no non-zero proper subspace with the same stability properties. Assume every infinite place of $K$ is real, let $N$ be a non-zero ideal of $\mathcal{O}_K$, and let $\chi=(\chi_v)_v$ assign to each infinite place $v$ a character of `rowIsometrySubgroup₀` of $K_v$. Fix a real place $w$ and $n\in\mathbb{Z}$ with $\chi_w=\mathrm{archWeightCharAt}\,h_w\,n$, the $n$-th power of the weight-one character at $w$, and let $\chi'$ assign to each $m\in\mathbb{Z}$ the family agreeing with $\chi$ away from $w$ and equal to $\mathrm{archWeightCharAt}\,h_w\,m$ at $w$. Let $y$ lie in $V$, be right invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, and lie in the archimedean type cut of the family `ArchTypeFamily.ofChar` $\chi$, i.e. transform by $\chi_v$ under the row-isometry subgroup at each infinite place. Put $\mathrm{lower}\,x=D_H x-i(D_E x+D_F x)$ and $\mathrm{raise}\,x=D_H x+i(D_E x+D_F x)$, where $D_d x(g)$ is the derivative at $t=0$ of $t\mapsto x(g\cdot \mathrm{archFlowAt}\,h_w\,d\,t)$. Then for every $j\in\mathbb{N}$ the $j$-th iterate $\mathrm{lower}^{[j]}y$ lies in $V$, is invariant under the same level group, and lies in the type cut of $\chi'(n-2j)$; likewise $\mathrm{raise}^{[j]}y$ lies in $V$, is level-invariant, and lies in the type cut of $\chi'(n+2j)$.
--
--   This is the $(\mathfrak{g},K)$-module statement that the Maass lowering and raising operators at a real place preserve a cuspidal constituent and its level, while shifting the weight of the archimedean type at that place by $-2$ and $+2$ respectively. It is used in the analysis of the Casimir eigenvalue on such constituents, in particular in the results isolating the discrete-series and holomorphic cases and in the passage to isotypic cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (χ' : ℤ → ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (hχ' : ∀ (m : ℤ) (v : InfinitePlace K), v ≠ w → χ' m v = χ v)
    (hχ'w : ∀ m : ℤ, χ' m w = archWeightCharAt hw m)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K (χ' (n - 2 * j)))) ∧
    (∀ j : ℕ, raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K (χ' (n + 2 * j)))) := by sorry
