-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/8eaecd09-1dc1-597d-bc50-2eeff377a917
-- title:
--   Base change of the twist 𝒪(D-rε) along ψ
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a separated morphism, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ\,\mathrm{id}$-compatibility $\varepsilon \cdot c=\mathbb 1$. Let $U\subseteq C$ be an open subscheme such that the composite of the inclusion $U\hookrightarrow C$ with $c$ is smooth of relative dimension $1$, and assume the set-theoretic image of $\varepsilon$ lies in $U$. Fix $r\in\mathbb N$ and two $R$-schemes $t\colon T\to\operatorname{Spec}R$, $t'\colon T'\to\operatorname{Spec}R$, together with $\psi\colon T'\to T$ satisfying $\psi$ followed by $t$ equals $t'$. Let $D$ be a relative effective Cartier divisor of degree $r$ on $c$ over $T$: an ideal sheaf datum $D.I$ on $C\times_{\operatorname{Spec}R}T$ whose associated closed subscheme is finite, flat and locally of finite presentation over $T$ via the second projection, with fibre rank $r$ at every point of $T$. Assume $D$ is supported in $U$, i.e. the support of $D.I$ is contained in the preimage of $U$ under the first projection. Then there exists an isomorphism of modules on $C\times_{\operatorname{Spec}R}T'$ between the twist module of the pulled-back divisor $D.\mathrm{pullbackAlong}\,\psi$ (whose ideal is the comap of $D.I$ along $\mathbb 1_C\times\psi$) and the pullback along $\mathbb 1_C\times\psi$ of the twist module of $D$. Here the twist module of a divisor $D$ over $T$ is the rigidification along the section $\mathrm{rigSection}\,c\,t\,\varepsilon$ and the projection to $T$ of $D.I^{\vee}\otimes(\mathcal I_\varepsilon^{\,r})$, where $\mathcal I_\varepsilon$ is the kernel ideal of that section and rigidification of $L$ means $L\otimes q^*\bigl((\sigma^*L)^{\vee}\bigr)$; the conclusion asserts nonemptiness of the type of such isomorphisms, not a designated one.
--
--   This is the compatibility of the rigidified line bundle $\mathcal O(D-r\varepsilon_T)$ with base change $\psi\colon T'\to T$, in a form where only an open $U$ of the curve is required to be smooth of relative dimension one over the base (and to contain the section and the support of the divisor), $c$ itself being merely separated — the situation of a semistable model with $U$ its smooth locus. It feeds the identification of the relative Picard functor with divisor data, being used in the construction of open charts for the relative sub-Picard presheaf and in the recognition of a divisor from an isomorphism of its twist module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {r : ℕ} {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) (hDU : D.SupportedIn U) :
    Nonempty ((D.pullbackAlong ψ.1 ψ.2).twistModule c ε ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj (D.twistModule c ε)) := by sorry
