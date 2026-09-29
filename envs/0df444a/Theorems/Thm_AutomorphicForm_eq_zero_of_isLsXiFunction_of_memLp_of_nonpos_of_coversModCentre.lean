-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre
-- name    : AutomorphicForm.eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5a4e19c8-d004-555d-8f1f-fe78e5a18ebb
-- title:
--   Vanishing of L² ξ-automorphic functions when c≤ 0
-- statement:
--   Let $F$ be a number field, $\mathcal{O}_F$ its ring of integers, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $c,u,d_1,d_2$ be real numbers and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite component `glFin g` lies in the integral subgroup `finiteIntegralGL2 (𝓞 F) F` and which satisfy, at every infinite place $w$ of $F$, with $g_w$ the image of $g$ under `glArch` followed by `archComponent F w`: $c\le \mathrm{localHeight}(g_w)=\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)$, $\mathrm{xWindowSq}(g_w)=\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-\mathrm{localHeight}(g_w)^2\le u^2$, and $\lVert\det g_w\rVert\in[d_1,d_2]$. Assume $c\le 0$, $d_1<d_2$, $u\ne 0$, and that $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z\in\mathbb{A}_F^\times$ with $\gamma g\,z \in D$ (images taken under `globalPoints` and `centralScalar`). Let $\xi$ be a homomorphism from the full subgroup $\top$ of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous, left invariant under $\mathrm{GL}_2(F)$, satisfy $\varphi(z g)=\xi(z)\varphi(g)$ for all central ideles $z$, and lie in $L^2$ of the adelic Haar measure `adelicGLHaar` restricted to $D$. Then $\varphi=0$.
--
--   This is the degenerate case of the $L^2$ theory on centre-cut Siegel windows: for $c\le 0$ the height condition $c\le\lVert\det\rVert/\mathrm{rowNormSq}$ imposes nothing, since heights are positive, and a covering window of that shape supports no nonzero continuous $\xi$-equivariant automorphic function that is square-integrable on it. It is used to dispose of the non-positive height floor in [`AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre`](thm.html#AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre) and in [`AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre`](thm.html#AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre), reducing their statements to windows with a positive height floor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.eq_zero_of_isLsXiFunction_of_memLp_of_nonpos_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : c ≤ 0) (hd : d₁ < d₂) (hu : u ≠ 0)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ) (hcont : Continuous φ)
    (hL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))) :
    φ = 0 := by sorry
