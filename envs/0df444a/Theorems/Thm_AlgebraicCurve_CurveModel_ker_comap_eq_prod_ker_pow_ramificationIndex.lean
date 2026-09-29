-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
-- name    : AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/dbc91557-9d47-555d-ba8a-a5fc4bace424
-- title:
--   Fibre multiplicities of a finite map of curve models
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields equipped with $k$-algebra structures, each satisfying `IsCurveOver k` (every nonzero element has a divisor of degree $0$ whose coefficient at each place $v$ is $\mathrm{ord}_v$, every place has residue field finite-dimensional over $k$, and $\Omega_{F/k}$ is free of rank one), and each essentially of finite type over $k$; assume $F'$ is an $F$-algebra, compatibly with $k$, and integral over $F$. Let $M$, $M'$ be curve models of $F$, $F'$: integral schemes $M.C$, $M'.C$ with proper, smooth of relative dimension one morphisms to $\operatorname{Spec} k$, identifications of $F$, $F'$ with their function fields over $k$, and bijections from closed points to places compatible with the stalk subrings, every finite set of points lying in an affine open. Let $\pi : M'.C \to M.C$ be finite, flat and locally of finite presentation with $\pi$ followed by $M.\mathrm{toBase}$ equal to $M'.\mathrm{toBase}$, and assume that whenever a $k$-point $y$ of $M'.C$ (a section of $M'.\mathrm{toBase}$) composed with $\pi$ is a $k$-point $x$ of $M.C$, the place of $y$ contracts along $F \to F'$ to the place of $x$. Then for every $k$-point $x$ of $M.C$, writing $v$ for its place, the inverse image along $\pi$ of the kernel ideal sheaf of $x$ equals $\prod_{w} (\ker y_w)^{e_w}$, the product over the finite set of places $w$ of $F'$ in the fibre of $v$, where $y_w$ is the $k$-point of $M'.C$ corresponding to $w$ and $e_w$ is the least positive integer of the form $\mathrm{ord}_w(f)$ with $0 \neq f \in F$.
--
--   This is the classical statement that the scheme-theoretic fibre of a finite morphism of smooth proper curves over a point has multiplicities equal to the ramification indices of the associated extension of function fields (Hartshorne IV.2.1, Stichtenoth III.1), here in the form of an identity of ideal sheaves on a curve model. It underlies the comparison of pullbacks of divisors and line bundles along such morphisms, and is used in the computations of degeneracy and Hecke pullbacks on models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v
set_option maxHeartbeats 800000 in

theorem AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    (x.1.ker).comap π =
      ∏ w ∈ (M.pointEquivPlace x).fiber F', ((M'.pointEquivPlace.symm w).1.ker) ^ (w.ramificationIndex F) := by sorry
