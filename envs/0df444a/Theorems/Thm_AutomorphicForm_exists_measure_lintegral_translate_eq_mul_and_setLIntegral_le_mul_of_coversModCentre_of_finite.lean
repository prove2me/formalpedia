-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
-- name    : AutomorphicForm.exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/64276031-e8ca-5463-aba4-557b1732e875
-- title:
--   Invariant mean square comparable to mass over a Siegel window
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$; assume $0<c$, $0<d_1<d_2$. Write $\mathfrak{S}=\mathtt{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ for the set of $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component lies in the full level-zero subgroup $\mathrm{finiteIntegralGL2}$ and whose archimedean component $g_w$ at every infinite place $w$ satisfies $c\le \|\det g_w\|/\mathrm{rowNormSq}(g_w)$, $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-(\|\det g_w\|/\mathrm{rowNormSq}(g_w))^2\le u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$, and put $D=\bigcup_{x\in T}\mathfrak{S}x$. Assume: $D$ covers modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g\,z\in D$ (images taken under `globalPoints` and `centralScalar`); and the Siegel-type finiteness that $\{\gamma\in\mathrm{GL}_2(F): \exists s\in\mathfrak{S},\ \gamma s\in\mathfrak{S}\}$ is finite. Let $\xi$ be a homomorphism from the whole group $\mathbb{A}_F^\times$ (as the subgroup $\top$) to $\mathbb{C}^\times$. Then there exist a Borel measure $\nu$ on $\mathrm{GL}_2(\mathbb{A}_F)$, a constant $M\in[0,\infty]$ with $M\ne\infty$, and $\chi:\mathrm{GL}_2(\mathbb{A}_F)\to[0,\infty]$ with $\chi(x)\notin\{0,\infty\}$ for all $x$ and $\chi(k)=1$ whenever $k$ has trivial archimedean component (lies in the kernel of `glArch`) and integral finite component, such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ with $\varphi(\gamma g)=\varphi(g)$ for $\gamma\in\mathrm{GL}_2(F)$ and $\varphi(zg)=\xi(z)\varphi(g)$ for central $z$, one has $\int|\varphi|^2\,d\nu\le M\int_{D}|\varphi|^2\,d\mu$, $\int_{D}|\varphi|^2\,d\mu\le M\int|\varphi|^2\,d\nu$ (with $\mu$ the adelic Haar measure `adelicGLHaar` restricted to $D$), and $\int|\varphi(yx)|^2\,d\nu(y)=\chi(x)\int|\varphi|^2\,d\nu$ for every $x$.
--
--   This is the measure-theoretic step producing, on continuous automorphic functions of central character $\xi$, a mean square that is two-sidedly comparable (uniformly in $\varphi$) to the square mass over the covering window $D$ and for which every right translation acts as a scaling by a finite positive factor, the factor being $1$ on elements of the standard integral subgroup with trivial archimedean component. It is used by [`AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite`](thm.html#AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite) and [`AutomorphicForm.exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite`](thm.html#AutomorphicForm.exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite), where unitarity arguments for the right regular representation are run in terms of square mass over Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ (ν : @Measure (AdelicGL2 (𝓞 F) F) (glBorel (Fin 2) (𝓞 F) F)) (M : ℝ≥0∞)
      (χ : AdelicGL2 (𝓞 F) F → ℝ≥0∞),
      M ≠ ⊤ ∧ (∀ x, χ x ≠ 0 ∧ χ x ≠ ⊤) ∧
      (∀ k ∈ finiteAdelicGL2Subgroup F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F → χ k = 1) ∧
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
              ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
                (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
              (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
            M * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ∧
        ∀ x : AdelicGL2 (𝓞 F) F,
          @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ (y * x)‖₊ : ℝ≥0∞) ^ 2) =
            χ x * @lintegral _ (glBorel (Fin 2) (𝓞 F) F) ν (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) := by sorry
