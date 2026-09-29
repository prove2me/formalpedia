-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq
-- name    : AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/246dccae-c397-5dfd-b0dd-eec9eba9b59d
-- title:
--   Places are determined by their moduli point under an isomorphism of models
-- statement:
--   Let $K$ be an algebraically closed field and $L$ a field equipped with a $K$-algebra structure, and let $\mathfrak M$ be a `CurveModel K L`: a scheme $\mathfrak M.C$ together with a morphism $\mathfrak M.\mathrm{toBase} : \mathfrak M.C \to \operatorname{Spec} K$ which is integral, proper and smooth of relative dimension $1$, a ring isomorphism $L \cong \mathfrak M.C.\mathrm{functionField}$ compatible with the map $K \to \mathfrak M.C.\mathrm{functionField}$ induced by $\mathfrak M.\mathrm{toBase}$, and a bijection from the closed points of $\mathfrak M.C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, distinct from $L$ itself, whose ideals are principal) matching stalks with valuation subrings, each finite set of points lying in an affine open. Via `𝔐.pointEquivPlace`, places of $L/K$ correspond to sections $p : \operatorname{Spec} K \to \mathfrak M.C$ of $\mathfrak M.\mathrm{toBase}$. Let $\pi_X : X \to B$ and $s : \operatorname{Spec} K \to B$ be morphisms of schemes and let $e : \mathfrak M.C \to X \times_B \operatorname{Spec} K$ be an isomorphism with $e$ followed by the second projection equal to $\mathfrak M.\mathrm{toBase}$. Then for places $P, Q$ of $L/K$, if the section attached to $P$ and the section attached to $Q$, each followed by $e$ and then by the first projection to $X$, are equal as morphisms $\operatorname{Spec} K \to X$, then $P = Q$.
--
--   This is the injectivity half of the dictionary sending a place of $L/K$ to a $K$-point of $X$, obtained by transporting the $K$-points of a smooth proper model along an isomorphism onto a fibre product $X \times_B \operatorname{Spec} K$. It is used in the Čerednik–Drinfeld moduli tower, where the moduli point of a representative object attached to a place is computed as this dictionary value and the moduli map is constant on isomorphism classes, so that equal moduli points force equal places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq.lean

import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (𝔐 : AlgebraicCurve.CurveModel K L)
    {X B : Scheme.{u}} (πX : X ⟶ B) (s : Spec (CommRingCat.of K) ⟶ B)
    (e : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX s) (he : IsIso e)
    (he_snd : e ≫ CategoryTheory.Limits.pullback.snd πX s = 𝔐.toBase)
    (P Q : Place K L)
    (h : (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s =
      (𝔐.pointEquivPlace.symm Q).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s) :
    P = Q := by sorry
