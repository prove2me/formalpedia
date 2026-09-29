-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
-- name    : AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a1aeee0b-bf1a-58f9-94d2-516f23589a35
-- title:
--   Uniform square-integral bound over unipotent translates high in a Siegel set
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A}_K$ and $\mathrm{GL}_2(\mathbb{A}_K)$ written `AdelicGL2`. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T\subset\mathrm{GL}_2(\mathbb{A}_K)$, and put $W=\bigcup_{x\in T}\{g x : g\in \Sigma(c,u,d_1,d_2)\}$, where $\Sigma(c,u,d_1,d_2)$ is the centre-cut Siegel set of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, $c\le \lVert\det\rVert/\mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq}-(\lVert\det\rVert/\mathrm{rowNormSq})^2\le u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume $W$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\cdot z I\in W$. Let $\chi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a homomorphism on the full unit group (no continuity assumed), $C\subset\mathrm{GL}_2(\mathbb{A}_K)$ compact, and $c',u',d_1',d_2'$ reals with $c'>0$, $d_1'>0$. Then there exist $T_1\in\mathbb{R}$, $A\in\mathbb{N}$ and $M\in\mathbb{R}$ such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $\varphi(\gamma g)=\varphi(g)$ for $\gamma\in\mathrm{GL}_2(K)$ and $\varphi(zI\cdot g)=\chi(z)\varphi(g)$ for $z\in\mathbb{A}_K^\times$, and every $x\in\Sigma(c',u',d_1',d_2')$ with $T_1<H(x)$, where $H(x)=\prod_v(\lVert\det\rVert/\mathrm{rowNormSq})^{\mathrm{mult}\,v}$ is the archimedean height of the archimedean component of $x$, one has $$\int^-_{\{n(t)xk\,:\,t\in\overline{\mathrm{box}},\,k\in C\}}\lVert\varphi\rVert^2\,d\mu\;\le\;\mathrm{ofReal}\bigl(M\,H(x)^A\bigr)\int^-_{W}\lVert\varphi\rVert^2\,d\mu,$$ with $n(t)$ the upper unipotent matrix of entry $t$, $\overline{\mathrm{box}}$ the closure of the adelic box, $\mu$ the Haar measure `adelicGLHaar`, and both integrals lower Lebesgue integrals of $\lVert\varphi\rVert_{\ge0}^2$ in $[0,\infty]$.
--
--   This is the uniform form of a Godement-type majorisation: the square mass of an automorphic-type function over the moving unipotent-times-compact region attached to a point high in a Siegel set is bounded, up to a power of the archimedean height, by its square mass over a fixed covering set, with the three constants $T_1,A,M$ depending only on $K$, the two Siegel parameter sets, $T$, $C$ and $\chi$, and not on $\varphi$ or $x$. It is cited in the derivation of the bounds for right convolution against a test function on cusp forms, [`AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre) and [`AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre.lean

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

theorem AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
          T₁ < archHeight K (glArch (𝓞 K) K x) →
            ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
              unipotentGL2 t * x * c) (closure (adelicBox K)) C,
                (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
              ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
                ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
                  (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
