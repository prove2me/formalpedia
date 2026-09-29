-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a9f119c7-ac76-566e-bb7a-5dbf41cf7709
-- title:
--   Irreducibility over one algebraically closed extension gives geometric irreducibility
-- statement:
--   Let $K$ be a field, $X$ a scheme and $f \colon X \to \operatorname{Spec} K$ a morphism of schemes (all in a fixed universe $u$), and let $k$ be an algebraically closed field equipped with a $K$-algebra structure. Assume that the fibre product of $f$ with the morphism $\operatorname{Spec} k \to \operatorname{Spec} K$ induced by the structure map $K \to k$ has irreducible underlying topological space, i.e. that $X_k = X \times_{\operatorname{Spec} K} \operatorname{Spec} k$ is irreducible (the hypothesis is an `IrreducibleSpace` instance on the chosen pullback). The conclusion is `GeometricallyIrreducible f`: for every field $L$ and every morphism $\operatorname{Spec} L \to \operatorname{Spec} K$, and every scheme $Z$ sitting in a pullback square over $f$ and that morphism, the underlying space of $Z$ is irreducible. Thus irreducibility after base change to the single algebraically closed extension $k$ already forces irreducibility of every base change of $f$ to a field-valued point of $\operatorname{Spec} K$; no hypothesis of finite type, separability or nonemptiness on $X$ is imposed.
--
--   This is the standard criterion for geometric irreducibility of a scheme over a field (as in EGA IV₂ 4.5.9): testing over one algebraically closed extension suffices. It is the counterpart, for arbitrary base field $K$, of the statement that an irreducible scheme over an algebraically closed field is geometrically irreducible, and it is used in the project to recognise geometric irreducibility of fibres — for instance in the characterisation of geometric irreducibility of the fibres of a proper smooth morphism via bijectivity on global sections, and in the openness of the locus of points whose base-changed fibres are irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyIrreducible f := by sorry
