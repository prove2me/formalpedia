-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit
-- name    : AlgebraicGeometry.Scheme.Modules.pullback_map_projectionMorphism_comp_counit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d441bbd8-473f-52fb-b3b0-fa50cad66fb2
-- title:
--   Projection morphism as the mate of ε ⊗ 1
-- statement:
--   Let $Z$ and $X$ be schemes and $i \colon Z \to X$ a morphism of schemes, and let $F$ be an object of the monoidal category $X.\mathrm{Modules}$ of modules on $X$. Write $\mathrm{pullback}\ i \dashv \mathrm{pushforward}\ i$ for the adjunction `pullbackPushforwardAdjunction i`, with counit $\varepsilon$. By definition, `projectionMorphismMate i F` is the composite $$(\mathrm{pullback}\ i)(\,(\mathrm{pushforward}\ i)(\mathbf 1_Z) \otimes F\,) \xrightarrow{\ \mu^{-1}\ } (\mathrm{pullback}\ i)((\mathrm{pushforward}\ i)(\mathbf 1_Z)) \otimes (\mathrm{pullback}\ i)(F) \xrightarrow{\ \varepsilon_{\mathbf 1_Z} \rhd\ } \mathbf 1_Z \otimes (\mathrm{pullback}\ i)(F) \xrightarrow{\ \lambda\ } (\mathrm{pullback}\ i)(F),$$ where $\mu$ is the monoidal structure isomorphism of the functor $\mathrm{pullback}\ i$ at the pair $((\mathrm{pushforward}\ i)(\mathbf 1_Z), F)$, $\mathbf 1_Z$ is the monoidal unit of $Z.\mathrm{Modules}$, and $\lambda$ is the left unitor; and `projectionMorphism i F` is the morphism $(\mathrm{pushforward}\ i)(\mathbf 1_Z) \otimes F \to (\mathrm{pushforward}\ i)((\mathrm{pullback}\ i)(F))$ obtained from this composite by the adjunction's hom-equivalence. The assertion is that applying the functor $\mathrm{pullback}\ i$ to `projectionMorphism i F` and then composing with $\varepsilon$ at $(\mathrm{pullback}\ i)(F)$ returns `projectionMorphismMate i F`.
--
--   This records the defining property of the projection morphism $\theta_F \colon i_*\mathcal O_Z \otimes F \to i_*i^*F$: it is the transpose, under $i^* \dashv i_*$, of the composite built from the counit and the monoidal structure of $i^*$, so that the counit recovers that composite. It is used by `isIso_pullback_map_projectionMorphism_iff`, which converts invertibility of $i^*\theta_F$ into a statement about that composite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_projectionMorphism_comp_counit.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_projectionMorphism_comp_counit
    {Z X : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) :
    (Scheme.Modules.pullback i).map (Scheme.Modules.projectionMorphism i F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app ((Scheme.Modules.pullback i).obj F) =
      Scheme.Modules.projectionMorphismMate i F := by sorry
