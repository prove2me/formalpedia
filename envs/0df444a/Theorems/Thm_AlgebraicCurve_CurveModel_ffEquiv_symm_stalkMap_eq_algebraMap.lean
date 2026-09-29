-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap
-- name    : AlgebraicCurve.CurveModel.ffEquiv_symm_stalkMap_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c818ddb7-91f6-5aa5-b751-304e9fadd944
-- title:
--   Place-compatible finite morphism induces the given function field embedding
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields equipped with $k$-algebra structures satisfying `IsCurveOver k` (the existence of principal divisors for every nonzero element, finiteness of $v$-residue fields over $k$ for every place $v$, and $\Omega_{F/k}$ free of rank one), each essentially of finite type over $k$, with $F'$ an $F$-algebra compatible with the $k$-structures and integral over $F$. Let $M$ be a `CurveModel k F` and $M'$ a `CurveModel k F'`: integral schemes $M.C$, $M'.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, together with ring isomorphisms $M.\mathrm{ffEquiv} : F \simeq k(M.C)$ and $M'.\mathrm{ffEquiv} : F' \simeq k(M'.C)$ compatible with the maps from $k$, bijections from closed points to places of $F$ (resp. $F'$) over $k$ under which the local ring at a closed point, transported into $F$ (resp. $F'$), is exactly the valuation subring of the corresponding place, and the property that every finite set of points lies in an affine open. Let $\pi : M'.C \to M.C$ be a morphism over $\operatorname{Spec} k$, i.e. $\pi$ followed by $M.\mathrm{toBase}$ equals $M'.\mathrm{toBase}$, which is finite, flat and locally of finite presentation, and assume $\pi$ is compatible with restriction of places on $k$-points: for all sections $y$ of $M'.\mathrm{toBase}$ and $x$ of $M.\mathrm{toBase}$ with $y$ followed by $\pi$ equal to $x$, the place of $F'$ attached to $y$ by `pointEquivPlace`, restricted along $F \to F'$ (the preimage of its valuation subring), equals the place of $F$ attached to $x$. Then for every point $p$ of $M'.C$ and every germ $s$ in the stalk of $M.C$ at $\pi(p)$, the element $M'.\mathrm{ffEquiv}^{-1}$ of the image of $\pi^{\#}_p(s)$ in $k(M'.C)$ equals the image under $F \to F'$ of $M.\mathrm{ffEquiv}^{-1}$ of the image of $s$ in $k(M.C)$.
--
--   This is a rigidity statement for morphisms of smooth proper curves over an algebraically closed field: a finite flat morphism which sends each $k$-point to the point lying under its place induces, on stalks read inside the function fields, precisely the prescribed embedding $F \hookrightarrow F'$ (at the generic point, the induced map of function fields is that embedding). It is used in the analysis of the kernel of the comap of places, where it is factored into local factors with ramification exponents, and in the construction of Galois frames for the Čerednik–Drinfeld moduli towers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap.lean

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

theorem AlgebraicCurve.CurveModel.ffEquiv_symm_stalkMap_eq_algebraMap
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (p : M'.C) (s : M.C.presheaf.stalk (π.base p)) :
    M'.ffEquiv.symm (algebraMap _ M'.C.functionField (π.stalkMap p s)) =
      algebraMap F F' (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) := by sorry
