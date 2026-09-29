-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f1efe852-b72a-59c8-87dd-d20178a822b7
-- title:
--   Invertibility and trivialisation of the rigidified twist 𝒪(D-rε)
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a separated morphism. Let $\varepsilon$ be a section of $c$, that is, a morphism $\varepsilon_1 : \operatorname{Spec} R \to C$ together with the equation $\varepsilon_1$ followed by $c$ equals the identity of $\operatorname{Spec} R$, and let $U \subseteq C$ be an open subscheme such that the inclusion $U \hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$, with the set-theoretic range of $\varepsilon_1$ contained in $U$. Let $r$ be a natural number, $t : T \to \operatorname{Spec} R$ an $R$-scheme, and let $D$ be a relative effective Cartier divisor of degree $r$ on $C \times_{\operatorname{Spec} R} T$ over $T$: a quasi-coherent ideal sheaf datum $D.I$ on the fibre product whose associated closed subscheme, mapped by $D.I$'s closed immersion followed by the second projection, is finite, flat and locally of finite presentation over $T$ with fibre rank exactly $r$ at every point of $T$. Assume $D$ is supported in $U$, i.e. the support of $D.I$ is contained in the preimage of $U$ under the first projection. Write $\sigma =$ `RelPicard.rigSection c t ε` for the induced section $T \to C \times_{\operatorname{Spec} R} T$ of the second projection, and let the twist module of $D$ be the rigidification $L \otimes \mathrm{pr}_2^{*}\bigl((\sigma^{*}L)^{\vee}\bigr)$ of $L = D.I^{-1} \otimes \bigl((\ker \sigma)^{r}\bigr)^{\text{module}}$, the tensor product of the inverse module of $D.I$ with the module of the $r$-th power of the ideal sheaf of the section $\sigma$. Then this twist module is invertible, in the sense that every point of $C \times_{\operatorname{Spec} R} T$ has an open neighbourhood $V$ on which the restriction along $V \hookrightarrow C \times_{\operatorname{Spec} R} T$ is isomorphic to the unit sheaf of modules of $V$; and, moreover, its pullback along $\sigma$ is isomorphic to the unit object of the monoidal category of modules on $T$.
--
--   This is the assertion that $\mathcal O(D - r\varepsilon_T)$, canonically rigidified along the section, is a line bundle on $C \times_R T$ with trivialised fibre along $\varepsilon_T$, in the setting where only an open subscheme $U$ of $C$ containing the section and the support of $D$ is required to be smooth of relative dimension one over $R$, $c$ itself being merely separated (as for a Deligne–Rapoport model and its smooth locus). It feeds the construction of charts for the relative Picard functor, being used in the statements about open charts for the relative sub-Picard presheaf and about the characterisation of twist modules with vanishing base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) (hD : D.SupportedIn U) :
    Scheme.Modules.IsInvertible (D.twistModule c ε) ∧
      Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c t ε)).obj (D.twistModule c ε) ≅
        𝟙_ T.Modules) := by sorry
