-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/2cafdf0b-b549-5167-b94a-438320919c5a
-- title:
--   Slab bound for flow derivatives of a cuspidal cut vector
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose component at each infinite place $v$ has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with `archDetNorm` $v$ $g\in[d_1,d_2]$ for all $v$; assume `CoversModCentre`, i.e. every $g$ can be brought into $D$ by left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar. Consider the carrier data `productionPinsOf` attached to $D$, to the level groups $U(\mathfrak{N})=$ `levelOne` $\mathfrak{N}\sqcap$ `finiteAdelicGL2Subgroup`, to the Hecke generators `heckeGen`, and to the box `adelicBox K`; its central group is all of $(\mathbb{A}_K)^\times$. Let $\xi$ be a character of that group into $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: a cusp subrepresentation (inside `cuspKFiniteSubmodule`, stable under right translation by the finite adelic subgroup and by the row-isometry subgroups at the infinite places, and under right convolution by factorizable archimedean-bifinite test functions), nonzero, and with no proper nonzero cusp subrepresentation. Assume $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{w_0}$ for all $z$ and some real $w_0$. Let $\mathfrak{N}\neq 0$ be an ideal of $\mathcal{O}_K$, let `tys` be an archimedean type family, let $w$ be a real place, and let $y$ lie in $V$, be invariant under right multiplication by $U(\mathfrak{N})$, and lie in the type-cut submodule `archCutSubmodule K tys`. Assume further that at every real place $v$ the function $y$ satisfies `HasArchCharacterAt₀` for the weight character `archWeightCharAt` of some integer exponent, and that at $w$ the exponent is the given integer $n$. Then for all reals $0<e_1<e_2$ there is a bound $B$ such that for every $g$ with $\mathrm{ideleNorm}(\det g)\in[e_1,e_2]$ one has $\|y(g)\|\le B$, $\|(D_d y)(g)\|\le B$ for each of the three flow directions $d\in\{H,E,F\}$ at $w$, and $\|(D_d D_{d'} y)(g)\|\le B$ for all pairs of directions, where $D_d\varphi(g)$ is the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\mathrm{archFlowAt}\,(d,t))$.
--
--   This is the classical boundedness of a cusp form together with its first and second Lie-algebra derivatives, in the adelic setting restricted to a slab $e_1\le\|\det g\|_{\mathbb{A}}\le e_2$ of determinant norms. It supplies the regularity needed for the symmetry of the Casimir operator and the adjointness of the raising and lowering operators at the real place $w$, and is used in [`AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt`](thm.html#AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
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
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d y g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' y) g‖ ≤ B) := by sorry
