-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper
-- name    : AlgebraicGeometry.exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/0084c670-d195-5727-b957-23cc64435849
-- title:
--   Extending a map from a nonempty open of a smooth curve to a proper scheme
-- statement:
--   Let $k$ be a field and let $C$, $Y$ be schemes. Suppose given a morphism $c : C \to \operatorname{Spec} k$ with $C$ integral and $c$ smooth of relative dimension $1$, and a morphism $g : Y \to \operatorname{Spec} k$ which is proper. Let $U$ be an open subscheme of $C$ whose underlying set is nonempty, and let $\psi : U \to Y$ be a morphism over $k$, in the sense that $\psi$ followed by $g$ equals the open immersion $U.\iota$ followed by $c$. Then there is a morphism $\nu : C \to Y$ which is again a morphism over $k$, i.e. $\nu$ followed by $g$ equals $c$, and which extends $\psi$, i.e. $U.\iota$ followed by $\nu$ equals $\psi$. No separatedness or finiteness hypothesis on $C$ beyond those implied by smoothness over $k$ is imposed, and the extension is asserted to exist but is not claimed unique.
--
--   This is the standard extension theorem for a morphism defined on a nonempty open subset of a smooth integral curve over a field with target a proper $k$-scheme (equivalently, a rational map from a smooth curve to a proper scheme is everywhere defined). It is used in the construction of families of smooth proper curves over an algebraically closed field in the good-reduction/Jacobian part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_eq_of_smoothOfRelativeDimension_one_of_isProper
    {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (g : Y ⟶ Spec (CommRingCat.of k)) [IsProper g]
    (U : C.Opens) (hU : (U : Set C).Nonempty) (ψ : (U : Scheme.{u}) ⟶ Y) (hψ : ψ ≫ g = U.ι ≫ c) :
    ∃ ν : C ⟶ Y, ν ≫ g = c ∧ U.ι ≫ ν = ψ := by sorry
