-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
-- name    : AlgebraicGeometry.RelEffCartierDiv.isAlgEquivZero_twistModule_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/61cabe70-e70f-502e-97a0-6341a608ae83
-- title:
--   Fibrewise algebraic equivalence to zero of the twist of D
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $r$ be a natural number, $t \colon T \to \operatorname{Spec} R$ an $R$-scheme, and $D$ a relative effective Cartier divisor of degree $r$ on $C \times_{\operatorname{Spec} R} T$ over $T$: an ideal sheaf datum $D.I$ on the fibre product whose associated closed immersion, followed by the projection to $T$, is finite, flat and locally of finite presentation, with fibre rank exactly $r$ at every point of $T$. Let $k$ be an algebraically closed field and $s \colon \operatorname{Spec} k \to T$ a $k$-point of $T$. Consider the module $D.\mathrm{twistModule}\,c\,\varepsilon$ on $C \times_{\operatorname{Spec} R} T$, namely the rigidification along the section $\mathrm{rigSection}\,c\,t\,\varepsilon$ of the tensor product of $D.I^{-1}$ with the module of the $r$-th power of the ideal of that section: the tensor product of that line bundle with the pullback, along the projection to $T$, of the dual of its restriction along the section. The assertion is that the pullback of this module along the projection $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k \to C \times_{\operatorname{Spec} R} T$ satisfies `IsAlgEquivZero` over the geometric fibre $\mathrm{fibreAt}\,c\,t\,s \colon (C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k \to \operatorname{Spec} k$; that is, there exist a $k$-scheme $h \colon T' \to \operatorname{Spec} k$ which is locally of finite type and geometrically integral, an invertible module $M$ on the fibre product of the geometric fibre with $T'$, and two sections $t_0, t_1$ of $h$, such that the base change of $M$ along $t_0$ is isomorphic to the structure sheaf and its base change along $t_1$ is isomorphic to the given module.
--
--   This places the class of $\mathcal{O}(D - r\varepsilon_T)$, for a relative effective divisor of degree $r$, in the algebraic-equivalence-zero part of the relative Picard functor on every geometric fibre — the statement that the Abel map $\mathrm{Div}^r \to \mathrm{Pic}$ lands in $\mathrm{Pic}^0$ in the construction of the Jacobian of a smooth proper curve. It is used in the construction of charts for the cut-out subfunctor $\mathrm{Pic}^0$ and in establishing properness and geometric connectedness of its representing scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.isAlgEquivZero_twistModule_fibre
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε)) := by sorry
