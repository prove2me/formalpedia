-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_fibre_eq_one_of_subsingleton_H1
-- name    : AlgebraicGeometry.RelPicard.finrank_H0_fibre_eq_one_of_subsingleton_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/61152105-5a97-5786-98f1-f81b82276798
-- title:
--   Vanishing of h¹ forces h⁰=1 on fibres of the twisted bundle
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$ over $\operatorname{Spec} R$, that is, a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Fix $r, e \in \mathbb{N}$ and a relative effective Cartier divisor $D_\gamma$ of degree $e$ for $c$ over the identity of $\operatorname{Spec} R$: a quasi-coherent ideal sheaf data on $C \times_R \operatorname{Spec} R$ whose associated closed subscheme is finite, flat and locally of finite presentation over the base, of fibre rank $e$ at every point. Assume the Euler-characteristic normalisation $h\chi$: for every algebraically closed field $k$, every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ and every cover of the fibre by two affine opens with affine intersection, the two-chart Čech complex of the restriction to that fibre of $\bigl((\ker \text{of the rigidifying section})^r\bigr)^{\vee} \otimes \mathcal{O}(-D_\gamma)$ — the module $\mathtt{sectionTwist}\,c\,\varepsilon\,r \otimes D_\gamma.\mathtt{idealModule}$ — satisfies $\dim_k H^0 - \dim_k H^1 = 1$ in $\mathbb{Z}$, where $H^0$ is the kernel and $H^1$ the cokernel of the difference of the two restriction maps. Let further $t : T \to \operatorname{Spec} R$, and let $L$ be a rigidified line bundle for $c, \varepsilon$ over $t$, i.e. an invertible module $L.L$ on $C \times_R T$ together with a trivialisation of its pullback along the rigidifying section, and assume `FibrewiseAlgEquivZero L`: over every algebraically closed $k$ and every $k$-point of $T$, the restriction of $L.L$ to the fibre is `IsAlgEquivZero`, namely interpolated by an invertible module on a product with a geometrically integral, locally of finite type parameter scheme whose restrictions at two base points are the unit module and that restriction of $L.L$. Finally let $k$ be a field (not assumed algebraically closed), $s : \operatorname{Spec} k \to T$ a $k$-point, $\mathcal{W}$ a cover of the fibre $C \times_R T \times_T \operatorname{Spec} k$ by two affine opens with affine intersection, and suppose the $H^1$ of the associated two-chart Čech complex of the restriction to that fibre of $L.L \otimes \bigl(\mathtt{sectionTwist}\,c\,\varepsilon\,t\,r \otimes (D_\gamma \text{ pulled back along } t).\mathtt{idealModule}\bigr)$ vanishes. Then the $k$-dimension of the corresponding $H^0$ equals $1$.
--
--   This supplies the $h^0 = 1$ input for the construction of charts on the relative Picard functor, where a rigidified line bundle algebraically equivalent to zero on geometric fibres is matched with a relative effective divisor via the twist by $r\varepsilon - D_\gamma$. It is used by both halves of that chart statement, [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1) and [`AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso`](thm.html#AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H0_fibre_eq_one_of_subsingleton_H1.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.finrank_H0_fibre_eq_one_of_subsingleton_H1
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (r e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover)
    (h1 : Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
      (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
      (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1 := by sorry
