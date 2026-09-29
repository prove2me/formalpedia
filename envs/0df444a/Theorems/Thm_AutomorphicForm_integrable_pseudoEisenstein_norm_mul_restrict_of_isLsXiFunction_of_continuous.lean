-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
-- name    : AutomorphicForm.integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/a903e583-2d74-5301-a359-dbff5285342e
-- title:
--   Integrability of θ_{|φ|}· f on a slab fundamental domain
-- statement:
--   Let $F$ be a number field, let $0 < d_1 < d_2$ be reals, and write $G = \mathrm{GL}_2(\mathbb{A}_F)$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`; the idele norm of a unit $x$ of $\mathbb{A}_F$ is the value of its distributive Haar character. Let $\Phi \subseteq G$ be contained in the slab $\{g : \|\det g\| \in [d_1,d_2]\}$ and be a fundamental domain for the image of $\mathrm{GL}_2(F)$ in $G$ acting on that slab, with respect to the Haar measure restricted to the slab. The relevant centre subgroup here is all of $\mathbb{A}_F^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $f : G \to \mathbb{C}$ be continuous, invariant under left translation by the global points $\mathrm{GL}_2(F)$, and satisfying $f(z g) = \xi(z) f(g)$ for scalar matrices $z$. Let $\varphi : G \to \mathbb{C}$ be a slab profile for $\xi$: measurable, invariant under left translation by unipotent matrices $n(x)$, $x \in \mathbb{A}_F$, and by global points of the Borel subgroup, transforming by $\xi$ under the centre, bounded on every slab $\{\|\det g\| \in [d_1,d_2]\}$ with $d_1 > 0$, and vanishing outside a band $a \le \mathrm{ht}(g) \le b$ with $a > 0$ of adelic height. Then the product of the pseudo-Eisenstein series of $g \mapsto \|\varphi(g)\|$, namely $\|\varphi(g)\| + \sum_{\beta \in F} \|\varphi(w\, n(\beta)\, g)\|$, with $f$ is integrable for the Haar measure restricted to $\Phi$.
--
--   This is the absolute-convergence input for the unfolding of a pseudo-Eisenstein series against a continuous automorphic function with central character, in the style of Godement's unfolding of $\theta_\varphi$ over $B(F)\backslash \mathrm{GL}_2(F)$. It is used by [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous), where it licenses the interchange of summation and integration for an $f$ that need not be square-integrable on $\Phi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integrable_pseudoEisenstein_norm_mul_restrict_of_isLsXiFunction_of_continuous
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : AutomorphicForm.IsLsXiFunction (𝓞 F) F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ f)
    (_hfc : Continuous f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ) :
    Integrable (fun g : AdelicGL2 (𝓞 F) F =>
        AutomorphicForm.pseudoEisenstein F (fun x => ((‖φ x‖ : ℝ) : ℂ)) g * f g)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := by sorry
