-- Prove2me | Theorems.Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
-- name    : AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/b2212a68-8d13-5917-9d54-f25f145892ef
-- title:
--   Holomorphy of the Bruhat Eisenstein series for an entire family
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the scaling character `distribHaarChar` of the additive group of $\mathbb{A}_F$ by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units. Assume $\alpha$ takes positive real values, i.e. $0<\alpha(x)$ for all $x$ (hypothesis $h\alpha$). Let $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be group homomorphisms that are unitary, meaning $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for all $x$. Let $\varphi\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, written $(s,g)\mapsto\varphi_s(g)$, satisfy: (i) for every $s$, $\varphi_s$ is an induced section for the pair of characters $\mu\cdot\alpha^{\,s+1/2}$ and $\nu\cdot\alpha^{-(s+1/2)}$ (where $\alpha^z(x)=\alpha(x)^z$ as a complex power), that is, $\varphi_s(bg)=\mu(b_{11})\alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry); (ii) $(s,g)\mapsto\varphi_s(g)$ is continuous on the product; (iii) for each $g$ the function $s\mapsto\varphi_s(g)$ is entire. Then for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ the function $$s\longmapsto \varphi_s(g)+\sum_{\xi\in F}\varphi_s\bigl(w\,n(\xi)\,g\bigr),$$ with $w=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ taken over the diagonal embedding $F\to\mathbb{A}_F$, is differentiable on the open half-plane $\{s:\operatorname{Re} s>1/2\}$.
--
--   This is the holomorphy, on the half-plane of absolute convergence, of the $\mathrm{GL}_2$ Eisenstein series attached to a family of induced sections, written out along the Bruhat decomposition as the identity term plus a sum over the transversal $\{w\,n(\xi):\xi\in F\}$; absolute convergence of the sum at each individual $s$ with $\operatorname{Re} s>1/2$ is supplied by [`AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half`](thm.html#AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half), while the present statement gives holomorphy in $s$. It is used in the analytic estimates for Eisenstein series (approximation by the constant term, and the Maass–Selberg computations for pseudo-Eisenstein inner products).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    DifferentiableOn ℂ
      (fun s : ℂ => φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      {z : ℂ | 1 / 2 < z.re} := by sorry
