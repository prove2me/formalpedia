-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat
-- name    : AlgebraicGeometry.RelPicard.isClosed_setOf_exists_fibreModule_iso_unit_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/ad002502-7359-5ab6-bc90-90f70ef684de
-- title:
--   Closedness of the trivial locus of a rigidified family
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme, and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism; let $\mathcal V$ be a two-affine open cover of $C$ (two affine opens $U_0,U_1$ with $U_0\sqcup U_1$ covering $C$ and $U_0\cap U_1$ affine), and $\varepsilon$ a section of $c$, that is a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Two hypotheses are imposed: first, for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\mathcal O)$, taken with the $A$-algebra structure coming from the second projection, is bijective; secondly, for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every module $L$ on $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ that is invertible (locally isomorphic to the unit module) and satisfies `IsAlgEquivZero` for the projection to $\operatorname{Spec}k$ — i.e. there are a geometrically integral scheme $T'$ locally of finite type over $k$, an invertible module $M$ on the base change of the fibre to $T'$, and two sections $t_0,t_1$ of $T'/k$ such that the restriction of $M$ along $t_0$ is isomorphic to the unit module and its restriction along $t_1$ to the pullback of $L$ — every nonzero morphism from the unit module to $L$ forces $L$ to be isomorphic to the unit module. Let further $t\colon T\to\operatorname{Spec}R$ be locally of finite type and let $L$ be a rigidified line bundle for $(c,\varepsilon,t)$: an invertible module $L.L$ on $C\times_{\operatorname{Spec}R}T$ together with a trivialisation of its pullback along the section $T\to C\times_{\operatorname{Spec}R}T$ determined by $\varepsilon$; assume `FibrewiseAlgEquivZero` for $L$, i.e. for every algebraically closed $k$ and every $s\colon\operatorname{Spec}k\to T$ the pullback of $L.L$ to $(C\times_{\operatorname{Spec}R}T)\times_T\operatorname{Spec}k$ satisfies `IsAlgEquivZero` over $\operatorname{Spec}k$. Then the set of points $x\in T$ for which there exist a field $k$ and a morphism $s\colon\operatorname{Spec}k\to T$ sending the closed point of $\operatorname{Spec}k$ to $x$ and such that the fibre module $\mathrm{fibreModule}\,c\,t\,s\,L.L$ is isomorphic to the unit module on $(C\times_{\operatorname{Spec}R}T)\times_T\operatorname{Spec}k$ is closed in $T$.
--
--   This is the closedness of the locus in the base where a rigidified family of line bundles, fibrewise algebraically equivalent to zero, becomes trivial on the fibre — the form of upper semicontinuity of $h^0$ used for relative Picard schemes of proper flat curves with a two-chart cover. It feeds the separatedness clause in the representability of the relative $\operatorname{Pic}^0$ functor cut out by algebraic equivalence to zero, via [`AlgebraicGeometry.RelPicard.isSeparated_of_representsRelSubPic_algEquivZeroCut_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.isSeparated_of_representsRelSubPic_algEquivZeroCut_of_bijective_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isClosed_setOf_exists_fibreModule_iso_unit_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isClosed_setOf_exists_fibreModule_iso_unit_of_flat
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : (pullback c x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd c x) L →
      ∀ s : 𝟙_ (pullback c x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback c x).Modules))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) :
    IsClosed {x : T | ∃ (k : Type u) (_ : Field k) (s : Spec (CommRingCat.of k) ⟶ T),
      s.base (IsLocalRing.closedPoint k) = x ∧
        Nonempty (fibreModule c t s L.L ≅ 𝟙_ (pullback (pullback.snd c t) s).Modules)} := by sorry
