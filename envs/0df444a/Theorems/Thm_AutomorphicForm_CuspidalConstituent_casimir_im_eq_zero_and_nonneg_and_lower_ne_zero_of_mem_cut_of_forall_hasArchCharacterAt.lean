-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
-- name    : AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/d43a32ad-3a08-51f7-85b0-a3f26bdc53a5
-- title:
--   Bargmann inequalities at a real place for cut vectors
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T}(\cdot\,x)[\,\text{centreCutSiegelSet}\ K\ c\ u\ d_1\ d_2]$ satisfies `CoversModCentre`: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g z \in D$; here the centre-cut Siegel set consists of those $g$ whose finite part is integral, with $\mathrm{localHeight}\ge c$ and $\mathrm{xWindowSq}\le u^2$ at each infinite place and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Take the carrier data `productionPinsOf` attached to $D$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap$ the kernel of the archimedean projection, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and the box `adelicBox`; since its $Z$ is the full idele unit group, $\xi$ is a character of $(\mathbb{A}_K)^\times$, assumed to satisfy $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for a real $w_0$. Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: a cusp subrepresentation (contained in `cuspKFiniteSubmodule`, stable under right translation by the finite adelic subgroup and by `rowIsometrySubgroup₀` at every infinite place, and under right convolution by factorizable archimedean bi-finite test functions), nonzero, and having no proper nonzero such subrepresentation. Let $N\neq 0$ be an ideal, `tys` an archimedean type family, $w$ a real infinite place, and $\lambda\in\mathbb{C}$ such that every $x\in V$ is archimedean smooth at $w$ and satisfies $\mathrm{archCasimirAt}_w\,x=\lambda x$, the Casimir operator being normalised as $-\bigl(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_{F}\bigr)$ in the flow derivatives at $w$. Let $y$ be a nonzero element of $V$ which is right invariant under $\mathrm{levelOne}(N)\sqcap$ the finite adelic subgroup and lies in the archimedean cut $\bigsqcap_v\bigsqcup_i \mathrm{archTypeSubmoduleAt}(v,\mathrm{tys.rep}\,v\,i)$, such that at every real place $v$ the predicate `HasArchCharacterAt₀` holds for $y$ with the weight character $\mathrm{archWeightCharAt}\,m$ for some $m\in\mathbb{Z}$, and at $w$ with weight $n\in\mathbb{Z}$. Then, writing $\mathrm{lower}\,x=D_Hx-i(D_Ex+D_{F}x)$ and $\mathrm{raise}\,x=D_Hx+i(D_Ex+D_{F}x)$ for the derivatives at $w$: $\lambda$ is real, $4\,\mathrm{Re}\,\lambda+n(n-2)\ge 0$, $4\,\mathrm{Re}\,\lambda+n(n+2)\ge 0$, and $\mathrm{lower}\,y\neq 0$ (respectively $\mathrm{raise}\,y\neq 0$) holds if and only if $4\,\mathrm{Re}\,\lambda+n(n-2)>0$ (respectively $4\,\mathrm{Re}\,\lambda+n(n+2)>0$).
--
--   These are the positivity and tower-continuation inequalities underlying Bargmann's classification of the unitary representations of $\mathrm{SL}_2(\mathbb{R})$, here for a weight-$n$ vector of a cuspidal constituent of $\mathrm{GL}_2$ over an arbitrary number field, at the level of functions on the adelic group. It feeds the classification of the archimedean component of a cuspidal constituent at a real place in [`AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt.lean

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

theorem AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_of_forall_hasArchCharacterAt
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
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (hy0 : y ≠ 0) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    lam.im = 0 ∧ 0 ≤ 4 * lam.re + n * (n - 2) ∧ 0 ≤ 4 * lam.re + n * (n + 2) ∧
      (lower y ≠ 0 ↔ 0 < 4 * lam.re + n * (n - 2)) ∧ (raise y ≠ 0 ↔ 0 < 4 * lam.re + n * (n + 2)) := by sorry
