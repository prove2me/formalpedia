-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range
-- name    : AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/8a9c527a-a25e-57c3-ad2b-9335383870f5
-- title:
--   K-points whose closure meets the special fibre extend to sections
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain carrying the `IsDiscreteValuationRing` structure) and let $K$ be a field which is an $R$-algebra and a fraction field of $R$, both in the same universe. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism which is separated, locally of finite type and quasi-compact. Let $x : \operatorname{Spec} K \to X$ be a morphism such that $x$ followed by $f$ equals the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map $R \to K$, i.e. $x$ is a $K$-valued point of $X$ over $R$. Assume furthermore that there is a point $z$ in the closure of the range of the underlying continuous map of $x$ (that is, in the closure of the image point of $x$) with $f(z)$ the closed point of $\operatorname{Spec} R$, so that the closure of the image of $x$ meets the special fibre. The conclusion is that there exists a morphism $s : \operatorname{Spec} R \to X$ with $s$ followed by $f$ the identity of $\operatorname{Spec} R$, and with the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $R \to K$ followed by $s$ equal to $x$; thus $x$ extends to an $R$-section of $f$.
--
--   This is the form of the valuative criterion of properness used in practice over a discrete valuation ring: a $K$-point of a separated, quasi-compact, locally finite-type $R$-scheme extends to a section precisely when its scheme-theoretic closure meets the special fibre. It is used for the variant in which the extension hypothesis is given by a local homomorphism out of a point, for the closedness of the range of a morphism in the absence of a section, and for the criterion describing the Néron extension condition on $J_0$ at $p$ in terms of the closure meeting the preimage of the closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_mem_closure_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_mem_closure_range
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hcl : ∃ z ∈ closure (Set.range x.base), f.base z = IsLocalRing.closedPoint R) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x := by sorry
