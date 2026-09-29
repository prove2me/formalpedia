-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
-- name    : AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/5caffc0f-d817-517d-9557-05071e8bb7a8
-- title:
--   Two-chart pole datum: every field-valued level set has rank m
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composition with $c$ is the identity of $\operatorname{Spec}R$. Let $U,V\subseteq C$ be open subsets, both affine, with $U\sqcup V=\top$, such that a point lies in $U$ exactly when it is not in the set-theoretic image of $\varepsilon$. Let $f\in\Gamma(C,U)$ and $g\in\Gamma(C,V)$ satisfy $U\sqcap V=C_{\mathrm{basicOpen}}(f)=C_{\mathrm{basicOpen}}(g)$, and assume the restrictions of $f$ and $g$ to $U\sqcap V$ have product $1$. Throughout, sections over an open $W$ carry the $R$-algebra structure $R\to\Gamma(C,W)$ obtained from $c$ via `Scheme.TwoAffineOpenCover.algebraOfHom`, namely the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism of $R$ followed by $c$ on sections from $\top$ to $W$. Let $m\in\mathbb{N}$ and assume: for every field $L$ that is an $R$-algebra, $\dim_L\bigl(L\otimes_R\Gamma(C,V)/(g)\bigr)=m$; the map $R[X]\to\Gamma(C,U)$, $X\mapsto f$, is a finite ring homomorphism; and likewise $R[X]\to\Gamma(C,V)$, $X\mapsto g$, is finite. Then for every field $L$ that is an $R$-algebra and every $x\in L$, $$\dim_L\Bigl(L\otimes_R\Gamma(C,U)\big/\bigl(1\otimes f-x\otimes 1\bigr)\Bigr)=m.$$
--
--   This is the constancy of the degree of the finite map determined by a function with a single pole of order $m$ along the section $\varepsilon$: the fibre over the point $f=x$ of any field-valued base point has the same length $m$ as the divisor cut out by $g$ on the other chart. It is the rank computation feeding [`AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank`](thm.html#AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum_of_forall_finrank), and is a version of the earlier statement for this setting in which the hypothesis that $\Gamma(C,V)/(g)$ be free of rank $m$ over $R$ is weakened to the assertion that its rank equals $m$ after base change to an arbitrary field over $R$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank L (L ⊗[R] (Γ(C, V) ⧸ Ideal.span {g})) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m := by sorry
