-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum
-- name    : AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/6c619cf2-125d-5d85-bdff-878614958ca5
-- title:
--   Level sets of a two-chart pole datum are free of rank m
-- statement:
--   Let $R$ be a local Noetherian commutative ring, and let $c : C \to \operatorname{Spec} R$ be a proper morphism of schemes which is smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $U, V \subseteq C$ be affine open subschemes with $U \sqcup V = C$ (that is, $U \vee V = \top$) such that a point of $C$ lies in $U$ exactly when it is not in the set-theoretic image of $\varepsilon$. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ be sections with $U \cap V$ equal both to the basic open set of $f$ in $U$ and to the basic open set of $g$ in $V$, and such that the restrictions of $f$ and $g$ to $U \cap V$ have product $1$. Let $m$ be a natural number. Throughout, $\Gamma(C,U)$ and $\Gamma(C,V)$ carry the $R$-algebra structures induced by $c$ (through the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism followed by $c$ on sections). Assume $\Gamma(C,V)/(g)$ is a free $R$-module with $\operatorname{finrank}_R = m$, and that the $R$-algebra maps $R[X] \to \Gamma(C,U)$, $X \mapsto f$, and $R[X] \to \Gamma(C,V)$, $X \mapsto g$, are finite ring homomorphisms. Then for every commutative local $R$-algebra $S$ and every $s \in S$, the $S$-module $S \otimes_R \Gamma(C,U) / (1 \otimes f - s \otimes 1)$ is module-finite, free, and of rank $m$.
--
--   This is the freeness-and-rank half of the passage from a two-chart pole datum on a smooth proper geometrically integral curve to a finite map datum of degree $m$: the function $f$, with a pole of exact order $m$ along the section $\varepsilon$, exhibits $\Gamma(C,U)$ as a finite flat $R[f]$-algebra whose level sets over local base rings are free of rank $m$. It is used in the construction of finite map data from a two-chart affine open cover, via [`AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum
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
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m := by sorry
