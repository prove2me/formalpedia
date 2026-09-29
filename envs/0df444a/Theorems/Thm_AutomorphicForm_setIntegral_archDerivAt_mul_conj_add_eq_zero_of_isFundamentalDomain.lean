-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
-- name    : AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ab535027-94a1-5412-808a-bdffb6fe76cb
-- title:
--   Skew-symmetry of real-place flow derivatives on a determinant slab
-- statement:
--   Let $K$ be a number field, $w$ a real infinite place of $K$ (witnessed by `hw : w.IsReal`), and $X$ one of the three directions `H`, `E`, `Fm` of `ArchDir`. Let $0 < e_1 < e_2$ be reals and write $S = \{g \in \mathrm{GL}_2(\mathbb{A}_K) : \|\det g\| \in [e_1,e_2]\}$, where $\|\cdot\|$ is `ideleNorm`, the value at an idele of the distributive Haar character of the adele ring, viewed as a real number. Let $\mathcal{F} \subseteq S$ be a measurable set which is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ under `globalPoints` (the map induced by $K \to \mathbb{A}_K$) on the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_K)$, for the Borel structure `glBorel`, restricted to $S$. Let $x, x' : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy $x(\gamma g) = x(g)$ and $x'(\gamma g) = x'(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ and all $g$, be continuous, and satisfy `IsArchSmoothAt hw`, i.e. for each $g$ the function $e \mapsto x(g \cdot \text{archRealLiftAt } hw\, e)$ is $C^\infty$ on the set of real $2\times 2$ matrices $e$ of nonzero determinant, and likewise for $x'$. Write $D_X\varphi(g) = \frac{d}{dt}\varphi(g\cdot \text{archFlowAt } hw\, X\, t)|_{t=0}$, the derivative along the one-parameter flow inserted at $w$ in direction $X$; assume $D_X x$ and $D_X x'$ are continuous, and that there is a real $B$ with $\|x(g)\|, \|x'(g)\|, \|D_X x(g)\|, \|D_X x'(g)\| \le B$ for every $g \in S$. Then $\int_{\mathcal{F}} \bigl(D_X x(g)\,\overline{x'(g)} + x(g)\,\overline{D_X x'(g)}\bigr)\, dg = 0$ for the measure `adelicGLHaar`.
--
--   This is the skew-adjointness of the Lie algebra action at a real place with respect to the Petersson pairing $\langle u,v\rangle_{\mathcal F} = \int_{\mathcal F} u\bar v$: each of the generators $H$, $E$, $F$ of $\mathfrak{sl}_2(\mathbb{R})$, acting by right translation along the corresponding one-parameter flow, satisfies $\langle D_X x, x'\rangle_{\mathcal F} = -\langle x, D_X x'\rangle_{\mathcal F}$ on a determinant slab. It feeds the self-adjointness of the archimedean Casimir operator for this pairing and the resulting $L^2$-bounds for iterated flow derivatives of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (X : ArchDir)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x x' : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hx' : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x' (globalPoints (𝓞 K) K γ * g) = x' g)
    (hxc : Continuous x) (hx'c : Continuous x')
    (hxs : IsArchSmoothAt hw x) (hx's : IsArchSmoothAt hw x')
    (hDx : Continuous (archDerivAt hw X x)) (hDx' : Continuous (archDerivAt hw X x'))
    (B : ℝ) (hB : ∀ g : AdelicGL2 (𝓞 K) K, ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖x g‖ ≤ B ∧ ‖x' g‖ ≤ B ∧ ‖archDerivAt hw X x g‖ ≤ B ∧ ‖archDerivAt hw X x' g‖ ≤ B) :
    ∫ g in 𝓕, (archDerivAt hw X x g * conj (x' g) + x g * conj (archDerivAt hw X x' g)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
