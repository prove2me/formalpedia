-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_of_tensorProduct_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/46102e03-0d90-55fd-97f3-1e75fa125ec2
-- title:
--   Split multisection yields d fibrewise distinct sections
-- statement:
--   Let $R$ be a commutative ring and $c\colon C \to \operatorname{Spec} R$ an arbitrary morphism of schemes (no smoothness, properness or properness-type hypothesis on $c$ is imposed). Let $R_0$ be an $R$-algebra, $B$ an $R_0$-algebra, and let $\iota\colon \operatorname{Spec} B \to \operatorname{pullback}(c, \operatorname{Spec}(R \to R_0))$ be a closed immersion into the fibre product $C \times_{\operatorname{Spec} R} \operatorname{Spec} R_0$, assumed to lie over $\operatorname{Spec} R_0$ in the sense that $\iota$ followed by the second projection $\mathrm{baseChange}$ equals the morphism $\operatorname{Spec}(R_0 \to B)$. Let $R'$ be simultaneously an $R$-algebra and an $R_0$-algebra, compatibly (scalar tower $R \to R_0 \to R'$), let $d$ be a natural number, and suppose given an $R'$-algebra isomorphism $\varphi\colon R' \otimes_{R_0} B \cong \prod_{i \in \mathrm{Fin}\, d} R'$, i.e. the base change of $B$ to $R'$ splits completely into $d$ copies of $R'$. The conclusion asserts the existence of a family $\sigma\colon \mathrm{Fin}\, d \to$ sections of the second projection $C \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$ — each $\sigma_i$ being a morphism $\operatorname{Spec} R' \to C \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ whose composition with that projection is the identity of $\operatorname{Spec} R'$ — such that for every field $k$ and every morphism $s\colon \operatorname{Spec} k \to \operatorname{Spec} R'$, the map $i \mapsto s$ followed by $\sigma_i$ is injective: the resulting $d$ points of $C_{R'}$ over $\operatorname{Spec} k$ are pairwise distinct.
--
--   This is the passage from a completely split multisection to a tuple of honest sections that remain distinct on every field-valued fibre, the geometric input needed to produce charts after a splitting base change. It is used in the construction of finite étale covers carrying chart sections for the relative Picard scheme, in both the field-valued and the general finite-map-data forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_sections_injective_of_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (R₀ : Type u) [CommRing R₀] [Algebra R R₀]
    (B : Type u) [CommRing B] [Algebra R₀ B]
    (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)) [IsClosedImmersion ι]
    (hι : ι ≫ baseChange R c R₀ = specMap R₀ B)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']
    (d : ℕ) (φ : (R' ⊗[R₀] B) ≃ₐ[R'] (Fin d → R')) :
    ∃ σ : Fin d → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'),
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective fun i => s ≫ (σ i).1 := by sorry
