-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
-- name    : AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/10f13cd1-31e6-54ec-8149-0641e54a028b
-- title:
--   Twisted divisor module commutes with base change
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} R$ be separated and smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$-composite equal to the identity of $\operatorname{Spec} R$. Let $r$ be a natural number, let $t \colon T \to \operatorname{Spec} R$ and $t' \colon T' \to \operatorname{Spec} R$ be $R$-schemes and let $\psi$ be an $R$-morphism $T' \to T$, i.e. a morphism whose composite with $t$ is $t'$. Let $D$ be a relative effective Cartier divisor of degree $r$ on $c$ over $t$: an ideal sheaf datum $I$ on $C \times_{\operatorname{Spec} R} T$ whose associated closed immersion followed by the second projection to $T$ is finite, flat and locally of finite presentation, with fibrewise rank $r$ at every point of $T$. Write $\Psi =$ `RelPicard.baseChangeSnd c ψ` for the induced morphism $C \times_R T' \to C \times_R T$ (identity on $C$, $\psi$ on the base), and let $D' =$ `D.pullbackAlong ψ.1 ψ.2` be the divisor on $C \times_R T'$ with ideal the $\Psi$-comap of $I$. The theorem asserts that the set of isomorphisms of sheaves of modules on $C \times_R T'$ between the twist of $D'$ and $\Psi^{*}$ of the twist of $D$ is nonempty, where the twist of a divisor $E$ over a base $s \colon S \to \operatorname{Spec} R$ is the rigidification, along the section $\sigma_S = (s \circ \varepsilon, \mathrm{id}_S) \colon S \to C \times_R S$ and the projection $C\times_R S \to S$, of $E.I^{-1} \otimes (\ker \sigma_S)^{r}$-module; rigidification of $L$ along $\sigma$ and $q$ means $L \otimes q^{*}((\sigma^{*}L)^{\vee})$.
--
--   This is the base-change compatibility of the line bundle $\mathcal{O}(D - r\,\varepsilon_T)$, rigidified along the zero section, which makes the Abel map from relative effective divisors of degree $r$ to the rigidified relative Picard functor of a smooth separated relative curve a morphism of functors. It is used in the construction of charts for the relative Picard presheaf, in the comparison of twists on fibres, and in the recognition of divisors from isomorphisms of their twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) :
    Nonempty ((D.pullbackAlong ψ.1 ψ.2).twistModule c ε ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj (D.twistModule c ε)) := by sorry
