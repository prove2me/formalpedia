-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
-- name    : AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/5ed8e780-db26-57b0-8374-1e2ab8b9e69b
-- title:
--   Casimir bound -(n²+2n)/16 ≤ Reλ at a complex place
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T}(\,\cdot\,x)(\,\text{centreCutSiegelSet}\ c\,u\,d_1\,d_2)$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left multiplication by $\mathrm{GL}_2(K)$ and right multiplication by central idele scalars; here the centre-cut Siegel set consists of those $g$ whose finite part lies in the integral subgroup, with $c \le \mathrm{localHeight}$ and $\mathrm{xWindowSq} \le u^2$ at every infinite place and with $\|\det\|_w(g) \in [d_1,d_2]$ at every infinite place. Work with the production data attached to $D$, with level subgroups $\mathrm{levelOne}(N)\cap\ker(\text{arch})$, Hecke generators at the finite places, and the adelic box as conditioning set; its central subgroup is all of $\mathbb{A}_K^\times$, so $\xi$ is a character $\mathbb{A}_K^\times \to \mathbb{C}^\times$. Let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for $\xi$: it lies in the $K$-finite cusp space, is stable under right translation by the finite-adelic subgroup and by the row-isometry subgroups at the infinite places and under right convolution by factorizable archimedean-bi-finite test functions, is non-zero, and has no proper non-zero such subspace. Assume an ideal $N\neq 0$ and an archimedean type family $\mathrm{tys}$ for which the intersection of $V$ with the space of functions right invariant under $\mathrm{levelOne}(N)\cap\ker(\text{arch})$ and with the type cut of $\mathrm{tys}$ is non-zero. Let $w$ be a complex place, $w_0$ a real number with $\|\xi(z)\| = \|z\|_{\mathbb{A}}^{w_0}$ for all ideles $z$, and $\lambda,\lambda'$ complex numbers such that every $x\in V$ is archimedean-smooth at $w$, has continuous first and second archimedean derivatives in all six directions $H,E,F,iH,iE,iF$, and satisfies $\mathrm{archCasimirAtComplex}\,x = \lambda x$ and $\mathrm{archCasimirBarAtComplex}\,x = \lambda' x$. Finally let $n$ be a natural number and let $F_0 \neq 0$ lie in $V$, be right invariant under $\mathrm{levelOne}(N')\cap\ker(\text{arch})$ for some non-zero ideal $N'$ and lie in the type cut of an archimedean type family $\mathrm{tys}'$, and satisfy the highest-weight conditions $D_{iH}F_0 = i n F_0$ and $D_{F}F_0 - D_{E}F_0 + i\,(D_{iE}F_0 + D_{iF}F_0) = 0$ at $w$. Then $-\bigl((n^2+2n)/16\bigr) \le \operatorname{Re}\lambda$.
--
--   This is the archimedean positivity (unitarity) bound at a complex place: the real part of the Casimir eigenvalue of a cuspidal constituent is bounded below in terms of the top circle weight $n$ of a highest-weight vector for the maximal compact at that place, the bound coming from skew-adjointness of the noncompact directions for the Petersson pairing over a fundamental domain in a determinant slab together with the value $-(n^2+2n)$ of the compact Casimir on such a vector. It feeds the estimate for Whittaker coefficients at a complex place in terms of powers of the norm at the infinite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate

theorem AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex
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
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x)
    (n : ℕ) (N' : Ideal (𝓞 K)) (hN' : N' ≠ ⊥) (tys' : AutomorphicForm.ArchTypeFamily K)
    (F₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hF₀ : F₀ ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N' ⊓ archCutSubmodule K tys')
    (hF₀0 : F₀ ≠ 0)
    (hwt : archDerivAtComplex hw .iH F₀ = (Complex.I * (n : ℂ)) • F₀)
    (hJ : archDerivAtComplex hw .Fm F₀ - archDerivAtComplex hw .E F₀
      + Complex.I • (archDerivAtComplex hw .iE F₀ + archDerivAtComplex hw .iFm F₀) = 0) :
    -(((n:ℝ)^2 + 2*(n:ℝ))/16) ≤ lam.re := by sorry
