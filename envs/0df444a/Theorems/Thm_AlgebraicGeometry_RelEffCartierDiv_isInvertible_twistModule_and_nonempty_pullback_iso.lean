-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso
-- name    : AlgebraicGeometry.RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/c963c57c-a0e5-5943-afda-cab500c931b4
-- title:
--   Twist of a relative effective divisor is rigidified invertible
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a separated morphism which is smooth of relative dimension $1$, let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity, let $r$ be a natural number, and let $t \colon T \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$. Let $D$ be a `RelEffCartierDiv c r t`: an ideal sheaf datum $I$ on the fibre product $C \times_{\operatorname{Spec} R} T$ such that the closed immersion of the associated subscheme followed by the second projection to $T$ is finite, flat and locally of finite presentation, with fibre rank equal to $r$ at every point of $T$. Write $\sigma =$ `RelPicard.rigSection c t ε` for the induced section $T \to C \times_{\operatorname{Spec} R} T$ of the second projection, determined by $t$ followed by $\varepsilon$ in the first coordinate and the identity in the second, and let $J = \sigma$'s kernel ideal sheaf. The module `D.twistModule c ε` is the rigidification of $M = I^{\vee} \otimes J^{r}$ (the inverse module of $I$ tensored with the module of the $r$-th power of $J$) along $\sigma$, namely $M \otimes \mathrm{pr}_T^{*}\bigl((\sigma^{*}M)^{\vee}\bigr)$. The assertion is twofold: this module is invertible, in the sense that every point of $C \times_{\operatorname{Spec} R} T$ has an open neighbourhood $U$ on which the restriction is isomorphic to the unit sheaf of modules of $U$; and its pullback along $\sigma$ is isomorphic to the monoidal unit of $T$'s modules, i.e. to $\mathcal O_T$.
--
--   This produces, from a relative effective divisor of degree $r$ on a smooth separated relative curve with a section, the rigidified line bundle $\mathcal O(D - r\,\varepsilon_T)$ underlying the Abel–Jacobi map from the divisor functor to the relative Picard functor. It is used in the construction of the Abel–Jacobi morphism, in the description of open charts of the relative sub-Picard presheaf by divisors, and in the properness and geometric connectedness statements for representing objects of the relative sub-Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) :
    Scheme.Modules.IsInvertible (D.twistModule c ε) ∧
      Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c t ε)).obj (D.twistModule c ε) ≅
        𝟙_ T.Modules) := by sorry
