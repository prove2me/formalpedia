-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf
-- name    : AlgebraicGeometry.Scheme.bijective_pi_map_of_fppf_sheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1d69fac0-38f0-5e54-ace7-5b0c36de081b
-- title:
--   An fppf sheaf turns Spec of a finite product into a product
-- statement:
--   Let $E$ be a sheaf of abelian groups on the big fppf site of schemes, that is, an object of `Sheaf Scheme.fppfTopology AddCommGrpCat` (the underlying presheaf takes values in additive commutative groups one universe level above that of the schemes), let $\iota$ be a finite index type and let $(A_i)_{i\in\iota}$ be a family of commutative rings indexed by $\iota$. The product ring $\prod_i A_i$ comes with the evaluation ring homomorphisms $\mathrm{ev}_i \colon \prod_j A_j \to A_i$, and applying $\operatorname{Spec}$ gives morphisms of schemes $\operatorname{Spec} A_i \to \operatorname{Spec}\bigl(\prod_j A_j\bigr)$. The assertion is that the map sending an element $x$ of the group $E\bigl(\operatorname{Spec}\prod_i A_i\bigr)$ to the family $\bigl(E(\operatorname{Spec}\mathrm{ev}_i)(x)\bigr)_{i\in\iota}$ in $\prod_i E(\operatorname{Spec} A_i)$ is bijective, as a map of underlying types. Only bijectivity of the underlying map of sets is asserted; no additivity statement is made, although the map is in fact a homomorphism.
--
--   This is the statement that a sheaf on the big fppf site takes a finite disjoint union of affine schemes, presented as the spectrum of the product of the coordinate rings, to the corresponding product of sections; it is the standard reduction used to recombine sections given separately on the members of a finite affine covering family. It is used in the proof that fppf-Amitsur-trivial classes admit sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.bijective_pi_map_of_fppf_sheaf
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1}) {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) :
    Function.Bijective (fun (x : ToType (E.obj.obj (op (Spec (CommRingCat.of (∀ i, A i)))))) (i : ι) =>
      E.obj.map (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i))).op x) := by sorry
