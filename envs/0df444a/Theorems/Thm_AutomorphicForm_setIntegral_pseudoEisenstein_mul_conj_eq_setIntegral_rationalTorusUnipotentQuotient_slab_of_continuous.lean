-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
-- name    : AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/a58e002b-fb34-51d5-9047-1ed90685c50e
-- title:
--   Unfolding a pseudo-Eisenstein series against a continuous automorphic function
-- statement:
--   Let $F$ be a number field, let $0 < d_1 < d_2$ be reals, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. Let $\Phi \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be contained in the determinant slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is the idele norm given by the module of the adelic Haar measure, and assume $\Phi$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$ restricted to that slab. Let $\xi$ be a homomorphism from the full unit group $(\mathbb{A}_F)^\times$ (the group $Z$ of the production pin data, which is $\top$) to $\mathbb{C}^\times$. Let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous, invariant under left multiplication by global points of $\mathrm{GL}_2(F)$, and satisfy $f(zg) = \xi(z) f(g)$ for central scalars $z$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a slab profile for $\xi$: measurable, invariant under left multiplication by $n(x)$ for every adele $x$ and by global points of the Borel subgroup (lower-left entry zero), transforming by $\xi$ under the centre, bounded on every slab $\|\det g\| \in [d_1',d_2']$ with $d_1' > 0$, and vanishing outside a band $a \le \mathrm{adelicHeight}(g) \le b$ with $a > 0$. Then $$\int_{\Phi} \Big(\varphi(g) + \sum_{\beta \in F} \varphi(w\, n(\beta)\, g)\Big)\,\overline{f(g)}\, d\mu(g) = \int_{\{q\,:\,\|\det q.\mathrm{out}\| \in [d_1,d_2]\}} \varphi(q.\mathrm{out})\,\overline{f_N(q.\mathrm{out})}\, d\nu_T(q),$$ where $\mu$ is the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, $w$ is the global Weyl element, $q$ runs over the orbit quotient of $\mathrm{GL}_2(\mathbb{A}_F)$ by `rationalTorusUnipotent F` (the join of `rationalTorus F` and `adelicUnipotent F`) with the measure `rationalTorusUnipotentQuotientMeasure F` obtained from $\mu$ and the Haar measure `rationalTorusUnipotentHaar F`, $q.\mathrm{out}$ is a chosen representative, and $f_N(g) = \int f(n(x) g)\, dx$ is taken against the adelic additive Haar measure conditioned on the adelic box, a probability measure.
--
--   This is the unfolding identity for a pseudo-Eisenstein series paired against an automorphic function: the Bruhat sum over $B(F)\backslash \mathrm{GL}_2(F)$ collapses the integral over a fundamental domain into an integral of $\varphi$ against the constant term $f_N$ over $T(F)N(\mathbb{A}_F)\backslash \mathrm{GL}_2(\mathbb{A}_F)$, restricted to the determinant slab. Here $f$ is assumed continuous with central character $\xi$ and no square-integrability, the form required for pairing with Eisenstein series on the unitary axis; it is used in the axis-continuation statement for such pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous.lean

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

theorem AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab_of_continuous
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
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (f g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    ∫ q in {q : AutomorphicForm.RationalTorusUnipotentQuotient F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂},
        φ q.out * starRingEnd ℂ (constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν unipotentGL2 f q.out)
      ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) := by sorry
