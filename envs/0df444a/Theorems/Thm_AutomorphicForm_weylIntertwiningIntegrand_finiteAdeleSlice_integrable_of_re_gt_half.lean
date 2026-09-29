-- Prove2me | Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
-- name    : AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/1e929d6d-a214-5dea-8f60-4baea23b7ddc
-- title:
--   Integrability of the Weyl intertwining integrand over finite adeles
-- statement:
--   Let $F$ be a number field, and equip the finite adele ring $\mathbb{A}_{F,f} =$ `FiniteAdeleRing (𝓞 F) F` with a measurable space structure which is the Borel structure of its topology, and let $\sigma$ be an additive Haar measure on it. Write $\alpha$ for the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the Mathlib module `distribHaarChar (AdeleRing (𝓞 F) F)` with values in $\mathbb{R}_{\ge 0}$, pushed into $\mathbb{R}^\times$, and assume $\alpha$ takes strictly positive real values (hypothesis $h\alpha$). The assertion is then: for all monoid homomorphisms $\mu,\nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ which are unitary, i.e. $\lVert \mu(x)\rVert = \lVert\nu(x)\rVert = 1$ for every idele $x$; for every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$; for every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is a section of the induced representation attached to the pair of characters $\mu\cdot\alpha^{\,s+1/2}$ and $\nu\cdot\alpha^{-(s+1/2)}$ (complex powers being formed from the positive reals $\alpha(x)$), meaning that $\varphi(b g) = \mu(b_{00})\alpha(b_{00})^{s+1/2}\,\nu(b_{11})\alpha(b_{11})^{-(s+1/2)}\,\varphi(g)$ for every $g$ and every $b$ in the subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ of matrices with vanishing lower-left entry, the diagonal entries being read as units of $\mathbb{A}_F$; and for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$: the function $$t \longmapsto \varphi\bigl(w\, n(0,t)\, g\bigr), \qquad t \in \mathbb{A}_{F,f},$$ is $\sigma$-integrable, where $w$ is the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the antidiagonal matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ over $F$ and $n(x) = \left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)$, evaluated at the adele with zero infinite component and finite component $t$.
--
--   This is the finite-adelic half of the classical absolute-convergence statement for the $\mathrm{GL}_2$ Weyl (intertwining) integral $M(s)\varphi(g) = \int_{\mathbb{A}_F} \varphi(w\,n(x)\,g)\,dx$ in the range $\operatorname{Re} s > 1/2$, restricted to the slice $x = (0,t)$ with $t$ running over the finite adeles. It is used in establishing the polynomial-decay bound for the Fourier-type integrals of Weyl-translated induced sections against additive characters ([`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`](thm.html#AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [σ.IsAddHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ)
      (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g)) σ := by sorry
