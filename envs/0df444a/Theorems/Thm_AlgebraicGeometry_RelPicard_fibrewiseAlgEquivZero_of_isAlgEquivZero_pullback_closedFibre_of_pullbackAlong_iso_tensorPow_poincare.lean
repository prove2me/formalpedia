-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
-- name    : AlgebraicGeometry.RelPicard.fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/56146b70-225a-528b-b55f-c02064ccfad6
-- title:
--   Fibrewise algebraic equivalence to zero over a discrete valuation ring
-- statement:
--   Let $A$ be a commutative ring, $c : C \to \operatorname{Spec} A$ a morphism of schemes and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} A \to C$ whose composite with $c$ is the identity). Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a section $D.\mathrm{zeroSection}$ of it, and assume the type `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D` is nonempty, i.e. there is a datum consisting of a rigidified line bundle (the Poincaré bundle) on $C \times_A D.P$ satisfying `FibrewiseAlgEquivZero`, a universal property for rigidified line bundles satisfying that condition, and a trivialisation along the zero section. Let $k$ be a field and an $A$-algebra, $O$ a discrete valuation domain with a ring map $\rho_O : A \to O$, and $to_\kappa : O \to k$ a surjective ring map with $to_\kappa \circ \rho_O$ the structure map $A \to k$. Let $bc : C \times_A \operatorname{Spec} k \to C \times_A \operatorname{Spec} O$ be a morphism commuting with the first projections and with the second projections via $\operatorname{Spec}(to_\kappa)$. Let $T'$ be a field which is a fraction field of $O$, let $y : \operatorname{Spec} T' \to D.P$ be a morphism over $\operatorname{Spec}$ of $A \to O \to T'$, let $n \in \mathbb{N}$, and let $M$ be a rigidified line bundle on $C \times_A \operatorname{Spec} O$ relative to $\varepsilon$, i.e. an invertible module $M.L$ on that pullback together with a trivialisation along the rigidifying section. Assume: (i) the pullback of $M.L$ along $bc$ satisfies `IsAlgEquivZero` for $C \times_A \operatorname{Spec} k \to \operatorname{Spec} k$, that is, there are a geometrically integral scheme $S$ locally of finite type over $\operatorname{Spec} k$, an invertible module $N$ on $(C \times_A \operatorname{Spec} k) \times_k S$ and two $k$-points $t_0, t_1$ of $S$ such that $N$ restricted along $t_0$ is isomorphic to the unit module and $N$ restricted along $t_1$ is isomorphic to the pullback of the given bundle; and (ii) the underlying module of the pullback of $M$ along $\operatorname{Spec}(O \to T')$ is isomorphic to the $n$-th tensor power of the underlying module of the pullback of the chosen Poincaré bundle along $y$. Then `FibrewiseAlgEquivZero M` holds: for every algebraically closed field $k'$ and every morphism $s : \operatorname{Spec} k' \to \operatorname{Spec} O$, the pullback of $M.L$ to the fibre of $C \times_A \operatorname{Spec} O \to \operatorname{Spec} O$ at $s$ satisfies `IsAlgEquivZero` over $\operatorname{Spec} k'$.
--
--   This is the specialisation step for the relative Picard functor over a discrete valuation ring: a rigidified line bundle on $C \times_A \operatorname{Spec} O$ belongs fibrewise to the subfunctor cut out by algebraic equivalence to zero as soon as its closed fibre does and its generic fibre is a tensor power of a point of that subfunctor. It is used in the construction, on the modular curve $X_1$, of rigidified line bundles satisfying `FibrewiseAlgEquivZero` together with the prescribed comparison with a tensor power of the Poincaré bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
    {A : Type u} [CommRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (D : RelativePic0Designation A c) (hrep : Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D))
    (k : Type u) [Field k] [Algebra A k]
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : A →+* O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k) (htoκs : Function.Surjective toκ)
    (bc : pullback c (specMap A k) ⟶ pullback c (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) D.toBase) (n : ℕ)
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom ρO)))
    (hclosed : IsAlgEquivZero (pullback.snd c (specMap A k)) ((Scheme.Modules.pullback bc).obj M.L))
    (hgen : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom (algebraMap O T')), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) (Spec.map (CommRingCat.ofHom ρO)))).L ≅
      (hrep.some.poincare.pullbackAlong y).L.tensorPow n)) :
    FibrewiseAlgEquivZero M := by sorry
