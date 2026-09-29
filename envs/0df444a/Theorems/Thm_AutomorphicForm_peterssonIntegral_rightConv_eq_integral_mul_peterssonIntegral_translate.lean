-- Prove2me | Theorems.Thm_AutomorphicForm_peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate
-- name    : AutomorphicForm.peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a56f5045-b909-536c-9301-b64d35eedac8
-- title:
--   Petersson pairing of a right convolution, by Fubini
-- statement:
--   Let $K$ be a number field, write $G = \mathrm{GL}_2(\mathbb A_K)$ for `AdelicGL2 (𝓞 K) K` equipped with its Borel structure and the Haar measure $dg =$ `adelicGLHaar (Fin 2) (𝓞 K) K`, assumed $\sigma$-finite, and let $\|\cdot\|$ be the idele norm [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of $\mathbb A_K$ at an idele. Fix $w \in \mathbb R$, a measurable set $\mathcal F \subseteq G$, and functions $\Phi, f, Y, X, \Psi, h : G \to \mathbb C$. Here $\langle x, y\rangle_{\mathcal F} = \int_{\mathcal F} x(g)\,\overline{y(g)}\,\|\det g\|^{-w}\,dg$ is `peterssonIntegral K w 𝓕` and $(\varphi * \varrho)(g) = \int_G \varphi(gx)\varrho(x)\,dx$ is `rightConv K`. The conclusion is a conjunction of two implications. First: if $(g,x) \mapsto \Phi(gx) f(x)\,\overline{Y(g)}\,\|\det g\|^{-w}$ is integrable for the product of $dg$ restricted to $\mathcal F$ with $dx$, then $\langle \Phi * f, Y\rangle_{\mathcal F} = \int_G f(x)\,\langle \Phi(\,\cdot\, x), Y\rangle_{\mathcal F}\,dx$. Second: if $(g,x) \mapsto X(g)\,\overline{\Psi(gx)h(x)}\,\|\det g\|^{-w}$ is integrable for the same product measure, then $\langle X, \Psi * h\rangle_{\mathcal F} = \int_G \overline{h(x)}\,\langle X, \Psi(\,\cdot\, x)\rangle_{\mathcal F}\,dx$.
--
--   This is the Fubini unfolding of the weighted Petersson pairing over $\mathcal F$ when one of its two arguments is a right convolution, expressing it as an integral over $G$ of pairings of right translates. It is used in the construction of Rankin–Selberg test data, where the two integrability hypotheses are supplied by the consumer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate.lean

import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.peterssonIntegral_rightConv_eq_integral_mul_peterssonIntegral_translate
    (K : Type) [Field K] [NumberField K]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K)]
    (w : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕 : MeasurableSet 𝓕)
    (Φ f Y X Ψ h : AdelicGL2 (𝓞 K) K → ℂ) :
    (Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) →
      peterssonIntegral K w 𝓕 (rightConv K Φ f) Y =
        ∫ x, f x * peterssonIntegral K w 𝓕 (fun g => Φ (g * x)) Y ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        X p.1 * (starRingEnd ℂ) (Ψ (p.1 * p.2) * h p.2) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
        (((adelicGLHaar (Fin 2) (𝓞 K) K).restrict 𝓕).prod (adelicGLHaar (Fin 2) (𝓞 K) K)) →
      peterssonIntegral K w 𝓕 X (rightConv K Ψ h) =
        ∫ x, (starRingEnd ℂ) (h x) * peterssonIntegral K w 𝓕 X (fun g => Ψ (g * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
