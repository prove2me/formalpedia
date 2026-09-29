-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackSection_dual_det_eq_zero_iff_not_isIso
-- name    : AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/73503d0d-fdfe-53ba-9b50-7c6188c00cd3
-- title:
--   Degeneracy locus of an equal-rank map as the zero locus of a section of (det E)^∨
-- statement:
--   Let $X$ be a scheme, $n$ a natural number, and $E$, $F$ two sheaves of modules on $X$ (objects of `X.Modules`). Assume that $E$ and $F$ both satisfy `IsLocallyFreeOfRank n`, i.e. every point of $X$ has an open neighbourhood $U$ such that the pullback of the sheaf along the inclusion $U \to X$ is isomorphic to the free sheaf of modules on $\mathrm{Fin}\,n$ (up to universe lifting). Let $\varphi \colon E \to F$ be a morphism of sheaves of modules, and assume that `det n F`, the $n$-th exterior power of $F$ (the sheafification of the presheaf $n$-th exterior power of the underlying presheaf of modules), admits an isomorphism to the monoidal unit $\mathcal O_X$. Then there exists a morphism $\theta \colon \mathcal O_X \to (\det{}^n E)^\vee$, where the dual is the internal hom $\underline{\mathrm{Hom}}(\det{}^n E, \mathcal O_X)$, with the following property: for every field $K$ in the ambient universe and every morphism $s \colon \operatorname{Spec} K \to X$, the pulled-back section $\mathcal O_{\operatorname{Spec} K} \to s^*\!\left((\det{}^n E)^\vee\right)$ obtained from $\theta$ by applying the pullback functor along $s$ and composing with the inverse of the canonical isomorphism $s^*\mathcal O_X \cong \mathcal O_{\operatorname{Spec} K}$ is zero if and only if $s^*\varphi \colon s^*E \to s^*F$ fails to be an isomorphism. Only the existence of such a $\theta$ is asserted; no formula for it is given.
--
--   This is the classical description of the degeneracy locus of a morphism between locally free modules of equal rank as the zero locus of a determinant section, here of the dual of $\det E$ under the trivialisation of $\det F$. It is used in the construction of the theta divisor of a Jacobian, via [`AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff`](thm.html#AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff), where the relevant morphism is the evaluation map on a Picard bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackSection_dual_det_eq_zero_iff_not_isIso.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso
    {X : Scheme.{u}} {n : ℕ} {E F : X.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) (hF : Scheme.Modules.IsLocallyFreeOfRank n F)
    (φ : E ⟶ F) (hdet : Nonempty (Scheme.Modules.det n F ≅ 𝟙_ X.Modules)) :
    ∃ θ : 𝟙_ X.Modules ⟶ Scheme.Modules.dual (Scheme.Modules.det n E),
      ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ X),
        Scheme.Modules.pullbackSection s θ = 0 ↔ ¬ IsIso ((Scheme.Modules.pullback s).map φ) := by sorry
