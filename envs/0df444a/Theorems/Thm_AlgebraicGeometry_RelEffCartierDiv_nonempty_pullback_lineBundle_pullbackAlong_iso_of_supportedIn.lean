-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/cc77195e-130a-5d2e-b373-59d1210ca14f
-- title:
--   Base change of 𝒪(E) for divisors supported in a smooth open
-- statement:
--   Fix a commutative ring $R$ and a separated morphism $c \colon C \to \operatorname{Spec} R$ of schemes, together with an open subscheme $U \subseteq C$ whose inclusion followed by $c$ is smooth of relative dimension $1$. Let $\rho$ be a natural number and let $E$ be a relative effective Cartier divisor for $c$ of degree $\rho$ over the identity of $\operatorname{Spec} R$: that is, an ideal sheaf datum $E.I$ on $C \times_R \operatorname{Spec} R$ whose closed subscheme, followed by the second projection, is finite, flat and locally of finite presentation with fibrewise rank $\rho$ at every point. Assume $E$ is supported in $U$, i.e. the support of $E.I$ is contained in the preimage of $U$ under the first projection. Let $t \colon T \to \operatorname{Spec} R$ and $t' \colon T' \to \operatorname{Spec} R$ be $R$-schemes and let $\psi$ be a morphism $T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Writing $E_T$ and $E_{T'}$ for the divisors obtained from $E$ by `pullbackAlong` $t$ and $t'$ respectively (comap of $E.I$ along the induced map of products), and $\mathcal O(E_T)$, $\mathcal O(E_{T'})$ for their line bundles, defined as the duals of the corresponding ideal modules, the conclusion asserts that the set of isomorphisms between the pullback of $\mathcal O(E_T)$ along `baseChangeSnd c ψ` $\colon C \times_R T' \to C \times_R T$ and $\mathcal O(E_{T'})$ is nonempty.
--
--   This is the base-change law $\psi_C^{*}\mathcal O(E_T) \cong \mathcal O(E_{T'})$ for the line bundle attached to a relative effective Cartier divisor supported in a smooth relative curve open, replacing the base-change compatibility of the one-section twist $\mathcal O(\rho\varepsilon_T)$ when a polarising divisor is used instead of a section. It is used in the construction of polarisation pairs and in the chart-by-chart analysis of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (E.pullbackAlong t (Category.comp_id t)).lineBundle ≅
      (E.pullbackAlong t' (Category.comp_id t')).lineBundle) := by sorry
