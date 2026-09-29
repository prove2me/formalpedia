-- Prove2me | Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
-- name    : AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c064790b-f58b-5ac2-a62e-c3d24f5460c0
-- title:
--   Automorphic functions are a.e. strongly measurable for adelic Haar measure
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}_F$ for its adele ring and $G = \mathrm{GL}_2(\mathbb{A}_F)$, equipped with the Borel $\sigma$-algebra `glBorel` of its topology and with the Haar measure `adelicGLHaar`. Let $d_1 < d_2$ be reals with $0 < d_1$, and let $\Phi \subseteq G$ be a set contained in the slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is the idele norm `ideleNorm`, the value of the distributive Haar character of $\mathbb{A}_F$ at an idele, read as a real number; assume $\Phi$ is a fundamental domain, in Mathlib's almost-everywhere sense, for the action of the image of $\mathrm{GL}_2(F)$ under the entrywise map `globalPoints` induced by $F \to \mathbb{A}_F$, with respect to `adelicGLHaar` restricted to that slab. Let `pins` be the bundle `productionPinsOf` formed from $\Phi$, the levels `levelOne`, the Hecke generators `heckeGen` and the box `adelicBox F`; its central subgroup is all of $\mathbb{A}_F^\times$. Let $\xi$ be a character of that subgroup with values in $\mathbb{C}^\times$ and $v : G \to \mathbb{C}$ a function satisfying `IsAutomorphicFnAt`, i.e. the predicate `LsXiMember` for these data, $\xi$ and $\Phi$. Then $v$ is almost-everywhere strongly measurable for `adelicGLHaar`. The proof uses none of the hypotheses on $d_1, d_2$, on $\Phi$ or on $v$; the conclusion is obtained for an arbitrary function $v$.
--
--   This is the measurability step that lets a $\xi$-equivariant square-integrable function on a truncation domain be treated as a measurable function on the whole adelic group, rather than only on the domain. It is used throughout the analysis of convolution operators, level-type averages and constant terms of automorphic functions on $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
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

theorem AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (_hv : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ v) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
