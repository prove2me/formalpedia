-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/fcefa87b-8290-5c15-9301-48243ff276fb
-- title:
--   Bargmann unitarity inequalities for a weight-n cut vector
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T}(\cdot\,x)[\,\text{centreCutSiegelSet } K\,c\,u\,d_1\,d_2\,]$ satisfies `CoversModCentre`: every $g$ can be written with $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (embedded adelically) and some central idelic scalar $z$. Take the carrier data `productionPinsOf` with domain $D$, level groups $N\mapsto \mathrm{levelOne}(N)\sqcap$ the finite-adelic subgroup, Hecke elements $\mathrm{heckeGen}(v)$ and box $\mathrm{adelicBox}$; its central subgroup is all of $\mathbb{A}_K^\times$. Let $\xi$ be a character of that subgroup with $\|\xi(z)\|=\|z\|^{w_0}$ for all ideles $z$, where $\|\cdot\|$ is the idele norm and $w_0\in\mathbb{R}$, and let $V$ be a $\xi$-cuspidal constituent: an irreducible member of the cuspidal $K$-finite submodule stable under right translation by the finite-adelic subgroup, by the row-isometry subgroups at the infinite places and under right convolution by factorizable archimedean-bifinite test functions. Assume all infinite places of $K$ are real. Let $N\neq 0$ be an ideal, let $\chi$ assign to each infinite place $v$ a character of $\mathrm{rowIsometrySubgroup}_0(K_v)$, let $w$ be a real place with $\chi_w=\mathrm{archWeightCharAt}$ of weight $n\in\mathbb{Z}$, and let $\mathrm{lam}\in\mathbb{C}$ be such that every $x\in V$ is smooth along the real flows at $w$ and satisfies $\Omega_w x=\mathrm{lam}\cdot x$ for the Casimir operator $\Omega_w=-\big(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_{F^-}\big)$ built from the flow derivatives at $w$. Let $y\neq 0$ lie in $V$, be invariant under right translation by $\mathrm{levelOne}(N)\sqcap$ the finite-adelic subgroup, and lie in the $\chi$-type cut submodule (the intersection over infinite places $v$ of the $\chi_v$-isotypic submodules). Then, with $\mathrm{lower}\,x=D_Hx-i(D_Ex+D_{F^-}x)$ and $\mathrm{raise}\,x=D_Hx+i(D_Ex+D_{F^-}x)$ at $w$: $\mathrm{lam}$ is real, $4\,\mathrm{Re}(\mathrm{lam})+n(n-2)\ge 0$, $4\,\mathrm{Re}(\mathrm{lam})+n(n+2)\ge 0$, and $\mathrm{lower}\,y\neq 0$ exactly when the first of these quantities is positive, $\mathrm{raise}\,y\neq 0$ exactly when the second is.
--
--   These are the positivity and tower-continuation conditions of Bargmann's classification of the unitary representations of $\mathrm{SL}_2(\mathbb{R})$, stated here for the weight-$n$ vectors of a cuspidal constituent at a real place, in terms of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ rather than abstract representations. They feed the trichotomy [`AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal`](thm.html#AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal), which separates the principal-series, discrete-series and trivial possibilities for the archimedean component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal.lean

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

theorem AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ))
    (hy0 : y ≠ 0) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    lam.im = 0 ∧ 0 ≤ 4 * lam.re + n * (n - 2) ∧ 0 ≤ 4 * lam.re + n * (n + 2) ∧
      (lower y ≠ 0 ↔ 0 < 4 * lam.re + n * (n - 2)) ∧ (raise y ≠ 0 ↔ 0 < 4 * lam.re + n * (n + 2)) := by sorry
