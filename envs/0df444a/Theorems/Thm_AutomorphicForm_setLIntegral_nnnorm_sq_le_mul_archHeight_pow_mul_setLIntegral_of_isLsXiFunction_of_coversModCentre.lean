-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
-- name    : AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/277e2acb-ed67-501b-8a65-515ad5eb00e3
-- title:
--   Square-mass bound on unipotent sweeps high in a Siegel set
-- statement:
--   Let $K$ be a number field, write $\mathbb{A}_K$ for its adele ring and $G=\mathrm{GL}_2(\mathbb{A}_K)$, and let $\mu$ denote `adelicGLHaar`, the Haar measure on $G$ for the Borel structure. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T\subseteq G$, and put $W=\bigcup_{x\in T}\{g x : g\in \Sigma(c,u,d_1,d_2)\}$, where $\Sigma(c,u,d_1,d_2)$ is the centre-cut Siegel set of elements $g$ whose finite part lies in `finiteIntegralGL2` and such that at every infinite place $w$ one has $c\le \mathrm{localHeight}$ of the $w$-component of the archimedean part of $g$ (that is, $|\det|/\mathrm{rowNormSq}$), $\mathrm{xWindowSq}$ of that component $\le u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$. Assume $W$ covers modulo the centre: for every $g\in G$ there are $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\,\mathrm{diag}(z,z)\in W$. Let $\chi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a homomorphism (no continuity assumed) and $\varphi:G\to\mathbb{C}$ continuous, left invariant under $\mathrm{GL}_2(K)$ and satisfying $\varphi(\mathrm{diag}(z,z)g)=\chi(z)\varphi(g)$. Let $C\subseteq G$ be compact and fix reals $c',u',d_1',d_2'$ with $c'>0$ and $d_1'>0$. Then there exist $T_1\in\mathbb{R}$, $A\in\mathbb{N}$ and $M\in\mathbb{R}$ such that for every $x\in\Sigma(c',u',d_1',d_2')$ whose archimedean height $H(x)=\prod_w \mathrm{localHeight}(x_w)^{\,[K_w:\mathbb{R}]}$ exceeds $T_1$, the lower Lebesgue integral of $\|\varphi\|^2$ over $\{n(t)xk : t\in\overline{\mathrm{box}},\,k\in C\}$, with $n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and $\overline{\mathrm{box}}$ the closure of the adelic box, is at most $\mathrm{ofReal}(M\,H(x)^A)$ times the lower Lebesgue integral of $\|\varphi\|^2$ over $W$, both integrals taken with respect to $\mu$ and valued in $[0,\infty]$.
--
--   This is the measure-theoretic core of the estimates for smoothing (right convolution) operators applied to an automorphic function high in a Siegel domain: the square mass over a unipotent sweep of a high point, translated by a compact set, is dominated by the global square mass over a fixed covering window, with a polynomial loss in the archimedean height. It is used in the proof of [`AutomorphicForm.exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre), and its proof draws on the finiteness of rational points in a compact adelic set, a counting bound for rational points in adelic boxes, and the separation property of high points of Siegel sets modulo the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre.lean

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

theorem AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) →
        ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) C,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
