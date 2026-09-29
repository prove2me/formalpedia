-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/3c2d7b28-5182-57a4-ad94-2f18ecb8eb47
-- title:
--   Polar differentials span under constant field extension
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with $F$ an algebra over $K$, $F'$ an algebra over $K'$, and all the algebra maps compatible (scalar-tower and commuting-scalar conditions for $K \to K' \to F'$ and $K \to F \to F'$), with $K$ and $K'$ algebraically closed, $F$ essentially of finite type over $K$ and $F'$ over $K'$, and both $F/K$ and $F'/K'$ curves in the project's sense: every nonzero function has a degree-zero principal divisor recording its orders at all places, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field (here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring). Assume $F$ is finitely generated over $K$ and $F'$ over $K'$ in the form: there is a transcendental element over the base whose adjunction makes the function field finite-dimensional; assume $K'$ adjoined to the image of $F$ in $F'$ is all of $F'$; and assume that at every place $v$ of $F/K$ and every place $w$ of $F'/K'$ the differential $\mathrm{d}\pi$ of a uniformizer spans the differentials over the function field. Let $S$ be any set of places of $F/K$ and let $S'$ be the set of places $w$ of $F'/K'$ whose valuation subring pulls back along $F \to F'$ to the valuation subring of some $v \in S$. Then every $\eta$ in $\mathrm{polarDifferentials}\ K'\ F'\ S'$ — that is, every $\eta \in \Omega_{F'/K'}$ which at each $w \notin S'$ is $f \cdot \mathrm{d}\pi_w$ with $f$ in the valuation ring of $w$, and at each $w \in S'$ is $f \cdot \mathrm{d}\pi_w$ with $\pi_w f$ in that valuation ring — lies in the $K'$-span of the image of $\mathrm{polarDifferentials}\ K\ F\ S$ under the base-change map `KaehlerDifferential.map K K' F F'` from $\Omega_{F/K}$ to $\Omega_{F'/K'}$.
--
--   This is the spanning half of the constant field extension theorem for differentials with at most simple poles along a prescribed set of places: the differentials on the base-changed curve with simple poles above $S$ are generated over $K'$ by those coming from the curve over $K$. Together with the companion inclusion of the image into the polar differentials upstairs it yields the combined statement [`AlgebraicCurve.map_mem_polarDifferentials_and_mem_span_image_of_constantFieldExtension_of_isAlgClosed`](thm.html#AlgebraicCurve.map_mem_polarDifferentials_and_mem_span_image_of_constantFieldExtension_of_isAlgClosed), and it is used in the construction of Cartier-fixed regular differentials over the extended constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mem_span_image_polarDifferentials_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] [SMulCommClass K' F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K' F']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (hdK : ∀ v : Place K F, v.DCoordGenerates) (hdK' : ∀ w : Place K' F', w.DCoordGenerates)
    (S : Set (Place K F)) :
    ∀ η ∈ polarDifferentials K' F'
          {w : Place K' F' | ∃ v ∈ S, w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring},
        η ∈ Submodule.span K'
          (KaehlerDifferential.map K K' F F' '' (polarDifferentials K F S : Set (Ω[F⁄K]))) := by sorry
