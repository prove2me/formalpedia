-- Prove2me | Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
-- name    : AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/bf91fbc0-beab-5b26-8aac-eaa0ccf1fac0
-- title:
--   Pseudo-Eisenstein series of a slab profile is automorphic
-- statement:
--   Let $F$ be a number field, $\mathbb{A}$ its adele ring, and write $G = \mathrm{GL}_2(\mathbb{A})$. Fix reals $d_1 < d_2$ with $0 < d_1$, and a set $\Phi \subseteq G$ contained in the determinant slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is the idele norm given by the module character [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), and assume $\Phi$ is a fundamental domain, in Mathlib's almost-everywhere sense, for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on $G$ with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let the carrier data be `productionPinsOf` for the domain $\Phi$, the level subgroups `levelOne`, the Hecke generators `heckeGen` and the box `adelicBox`; its centre subgroup is all of $\mathbb{A}^\times$, its measurable structure and measure are the Borel structure `glBorel` and `adelicGLHaar`, and the additive datum is additive adelic Haar measure conditioned on `adelicBox`. Let $\xi$ be a group homomorphism from this centre to $\mathbb{C}^\times$, and let $\varphi : G \to \mathbb{C}$ satisfy `IsSlabProfile`: $\varphi$ is measurable, invariant under left multiplication by adelic unipotents $n(x)$ and by the global points of the lower-left-zero Borel subgroup, satisfies $\varphi(z g) = \xi(z)\varphi(g)$ for central $z$, is bounded on every slab $\{\|\det g\| \in [d_1',d_2']\}$ with $d_1' > 0$, and vanishes outside a band $a \le \mathrm{adelicHeight}(g) \le b$ with $a > 0$. The conclusion is that the pseudo-Eisenstein series $g \mapsto \varphi(g) + \sum_{\beta \in F} \varphi(w\, n(\beta)\, g)$ satisfies the predicate `IsAutomorphicFnAt` for these carrier data and $\xi$, i.e. membership in `LsXiMember` relative to the Borel structure, Haar measure, centre $\mathbb{A}^\times$ and domain $\Phi$.
--
--   This is the automorphy statement for incomplete (pseudo-)Eisenstein series built from a slab profile: left invariance under the global points, the prescribed central character, and square-integrability over a fundamental domain inside a determinant slab. It feeds the spectral analysis on $\mathrm{GL}_2$ over $F$, in particular the constant-term criterion and the continuation and Paley–Wiener statements for pseudo-Eisenstein series that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

theorem AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ) :
    IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ (AutomorphicForm.pseudoEisenstein F φ) := by sorry
