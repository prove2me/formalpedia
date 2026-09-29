-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
-- name    : AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/fb585002-01e7-5d63-bc5e-7c8731a360d8
-- title:
--   Raising and lowering operators on a cuspidal constituent
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$; write $D=\bigcup_{x\in T}\{g x: g\in\text{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$, the centre-cut Siegel set consisting of those $g$ whose finite part is integral, whose archimedean components at every infinite place have local height $\ge c$, have $x$-window square $\le u^2$ and archimedean determinant norm in $[d_1,d_2]$. Assume `CoversModCentre K D`: for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele scalar $z$ with $\gamma g\,z\in D$. Let `pins` be the production carrier data on $D$ with levels $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(v)$, Borel structures and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, central subgroup $\top$, and the adelic additive measure conditioned on `adelicBox K`; let $\xi$ be a character of that central subgroup and $V$ a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for $(\mathrm{pins},\xi)$, i.e. `IsCuspSubrep` holds for $V$, $V\neq 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let `tys` be an archimedean type family (a number $\mathrm{card}\,v$ of types together with representations $\mathrm{rep}\,v\,i\in\mathrm{ArchRepAt}\,K\,v$ at each infinite place $v$), let $w$ be a real place, and let $y$ lie in $V$, be invariant under right multiplication by $U(N)$, and lie in $\bigsqcap_v\bigsqcup_i$ `archTypeSubmoduleAt` of the types of `tys`. Assume at every real place $v$ some integer $m$ has `HasArchCharacterAt₀ K v (archWeightCharAt hv m) y` (transformation by the $m$-th power of `archWeightOneAt hv` on `rowIsometrySubgroup₀` of $K_v$), and that $y$ has this property at $w$ with integer $n$. Define, with `archDerivAt hw d φ g` the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\mathrm{archFlowAt}\,hw\,d\,t)$, the operators $\mathrm{lower}=D_H-i(D_E+D_{F^-})$ and $\mathrm{raise}=D_H+i(D_E+D_{F^-})$ at $w$. The conclusion is that for every $j\in\mathbb{N}$, $\mathrm{lower}^{j}y$ lies in $V$, is $U(N)$-invariant and lies in the archimedean cut submodule of some type family $\mathrm{tys}'$; it has the same character as $y$ at every real place $v\neq w$ at which $y$ has one; and it satisfies `HasArchCharacterAt₀` at $w$ with integer $n-2j$. The same three assertions hold for $\mathrm{raise}^{j}y$, with $n+2j$ at $w$.
--
--   This is the $(\mathfrak{g},K)$-module structure of a cuspidal constituent expressed at the level of functions: the Maass lowering and raising operators at a real place move a vector of weight $n$ to vectors of weights $n\mp 2j$ inside the same constituent, preserving the level at $N$, membership in some archimedean type family, and the weights at the other real places; the output type family is only asserted to exist. It feeds the analysis of the Casimir eigenvalue of a cuspidal constituent (reality and positivity, and the discrete-series or trivial alternatives) and the assembly of the core hypotheses used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt.lean

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

theorem AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (lower^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2 * j)) (lower^[j] y)) ∧
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (raise^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2 * j)) (raise^[j] y)) := by sorry
