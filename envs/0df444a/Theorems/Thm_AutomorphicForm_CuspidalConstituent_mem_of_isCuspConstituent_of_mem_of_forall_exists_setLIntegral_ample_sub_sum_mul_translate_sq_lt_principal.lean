-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
-- name    : AutomorphicForm.CuspidalConstituent.mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/8a6de7b0-f9c5-5c99-81ad-625e4d0887b5
-- title:
--   Mean-square approximation forces membership in a cuspidal constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be reals with $d_1<d_2$, $1\le\kappa$, $0<c$, $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $\mathfrak S(c,u,d_1,d_2)$ for the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c\le\mathrm{localHeight}$ and $\mathrm{xWindowSq}\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$; the ample variant $\mathfrak S^{a}(c,u,d_1,d_2,\kappa)$ imposes in addition $\mathrm{localHeight}_w(g)\le\kappa\,\mathrm{localHeight}_{w'}(g)$ for all pairs $w,w'$. Assume the union $W^{a}=\bigcup_{x\in T}\mathfrak S^{a}(c,u,d_1,d_2,\kappa)x$ covers modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in W^{a}$ (image of $\gamma$ taken under `globalPoints`, $z$ acting through `centralScalar`). Let the pins attached to the plain union $W=\bigcup_{x\in T}\mathfrak S(c,u,d_1,d_2)x$ be `productionPinsOf` with level groups $N\mapsto \mathrm{principalLevel}(N)\sqcap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto\mathrm{heckeGen}(v)$, adelic box $B$, Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ and the box-conditioned additive Haar measure on $\mathbb{A}_F$; its central group is all of $\mathbb{A}_F^\times$, and $\xi$ is a character of it with values in $\mathbb{C}^\times$. Let $N\ne 0$ be an ideal of $\mathcal O_F$, $\mathrm{tys}$ an archimedean type family (a number of types `card w` and representations `rep w i` at each infinite place $w$), and $V$ a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ that is a cuspidal constituent at these plain pins for $\xi$: $V$ satisfies `IsCuspSubrep`, $V\ne 0$, and every submodule $W\le V$ satisfying `IsCuspSubrep` is $0$ or $V$. Let $\varphi_1\in V$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous, satisfy `IsCuspAutomorphicFnAt` for $\xi$ at the pins attached to the ample union $W^{a}$ together with `IsKfSmooth`, be right invariant under $\mathrm{principalLevel}(N)\sqcap\ker(\mathrm{glArch})$, and lie in $\bigsqcap_{w}\bigsqcup_{i<\mathrm{card}\,w}\mathrm{archTypeSubmoduleAt}(w,\mathrm{rep}\,w\,i)$. Assume finally that for every $\varepsilon\in[0,\infty]$ with $\varepsilon>0$ there are a finite set $s$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ and scalars $l(h)$ with $\int^{-}_{W^{a}}\bigl\|\varphi(y)-\sum_{h\in s}l(h)\varphi_1(yh)\bigr\|^2\,dy<\varepsilon$ for the Haar measure. Then $\varphi\in V$.
--
--   This is the closure step in the strong multiplicity one argument for $\mathrm{GL}_2$ over a number field: a typed, principal-level-invariant smooth cusp function that is approximated in mean square on an ample Siegel window by finitely many right translates of a single member of a cuspidal constituent already belongs to that constituent. Deliberately of mixed grain, the approximation premise and the automorphy of $\varphi$ are stated at the ample window while the constituent, the level condition and the conclusion are at the plain window; it is used by [`AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre`](thm.html#AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.CuspidalConstituent.mem_of_isCuspConstituent_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ₁ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁ : φ₁ ∈ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ)
    (hφN : φ ∈ AutomorphicForm.CuspidalConstituent.levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (hφt : φ ∈ archCutSubmodule F tys)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ y - ∑ h ∈ s, l h * φ₁ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε) :
    φ ∈ V := by sorry
