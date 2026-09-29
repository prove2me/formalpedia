-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum
-- name    : AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a91d1931-4e7d-5185-9f3c-18e4b67f63c4
-- title:
--   Degree m of the level sets of f at every field point
-- statement:
--   Let $R$ be a commutative local Noetherian ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity of $\operatorname{Spec} R$. Let $U, V$ be open subschemes of $C$, both affine, with $U \sqcup V = C$ as opens, and with $U$ the set-theoretic complement of the image of the section: a point of $C$ lies in $U$ exactly when it is not in the range of the underlying map of $\varepsilon$. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ satisfy $U \cap V = C_f = C_g$ (the basic opens of $f$ and of $g$), and let the restrictions of $f$ and $g$ to $U \cap V$ have product $1$. Throughout, $\Gamma(C,U)$ and $\Gamma(C,V)$ carry the $R$-algebra structures induced by $c$ through $R \cong \Gamma(\operatorname{Spec} R, \top) \to \Gamma(C,U)$, resp. $\to \Gamma(C,V)$. Let $m \in \mathbb{N}$ and assume $\Gamma(C,V)/(g)$ is a free $R$-module of rank $m$, and that $R[X] \to \Gamma(C,U)$, $X \mapsto f$, and $R[X] \to \Gamma(C,V)$, $X \mapsto g$, are finite ring maps. Then for every field $L$ that is an $R$-algebra and every $x \in L$,
--   $$\dim_L \bigl(L \otimes_R \Gamma(C,U)\bigr)\big/\bigl(1 \otimes f - x \otimes 1\bigr) = m .$$
--
--   This is the statement that a two-chart pole datum $(f,g)$ whose pole divisor along the section has order $m$ has degree exactly $m$ at every $L$-valued point of the affine line, the fibre dimension being computed on the other chart as $\dim_L L \otimes_R \Gamma(C,V)/(g)$. It supplies the constant-rank input to [`AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum`](thm.html#AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum), which deduces freeness of $\Gamma(C,U)$ over $R[f]$ from finiteness together with constancy of the fibre dimensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
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
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (L : Type u) [Field L] [Algebra R L] (x : L) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m := by sorry
