-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
-- name    : AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9720d27e-4e91-5a29-a801-9d61883e1b41
-- title:
--   Uniform L²-mass bound over a compact set
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $S$ for the centre-cut Siegel set with parameters $c,u,d_1,d_2$, namely the set of $g\in \mathrm{GL}_2(\mathbb{A}_K)$ whose finite component lies in the full level-zero subgroup $\mathrm{GL}_2$ of the finite adeles and which satisfies, at every infinite place $w$ of $K$, the three conditions $c\le \lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)$, $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-(\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w))^2\le u^2$, and $\lVert\det g_w\rVert\in[d_1,d_2]$, where $g_w$ denotes the image of $g$ at $w$. Put $W=\bigcup_{x\in T} Sx$, and assume $W$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\cdot z\mathbf{1}\in W$. Let $\chi$ be a homomorphism from the full group of ideles of $K$ to $\mathbb{C}^\times$, and let $R\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be compact. Then there is a real number $N$ such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $\varphi(\gamma g)=\varphi(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ and $\varphi(z\mathbf{1}\cdot g)=\chi(z)\varphi(g)$ for all ideles $z$, one has $\int_R^{-}\lVert\varphi\rVert^2\,d\mu\le \mathrm{ofReal}(N)\cdot\int_W^{-}\lVert\varphi\rVert^2\,d\mu$, the lower Lebesgue integrals being taken in $[0,\infty]$ against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the measure-theoretic comparison step underlying Godement-type estimates for automorphic forms: the $L^2$-mass of an admissible function over an arbitrary compact set is dominated by its mass over a fixed covering Siegel window, with a constant depending on the window, the central character and the compact set but not on the function. It feeds the results on translate spans, smoothing operators on cuspidal functions, and the comparison of archimedean occurrence classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal NNReal

theorem AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hR : IsCompact R) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal N *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
