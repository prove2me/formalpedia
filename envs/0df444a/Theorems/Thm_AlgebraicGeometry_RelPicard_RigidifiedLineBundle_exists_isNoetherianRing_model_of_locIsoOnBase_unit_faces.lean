-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/3986c8a8-e7c6-58bf-bab4-06ff7b427e3f
-- title:
--   Noetherian descent for a rigidified bundle with trivial faces
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, with multiplication, unit and inverse, the group axioms, and naturality of multiplication in $T$), and assume the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth and proper, every fibre of $f$ over a point of $\operatorname{Spec} S$ is connected, and $f$ carries a relative group law. Let $M$ be a rigidified line bundle on the triple product, i.e. an invertible module $M.L$ on $\operatorname{pullback}(\mathrm{prodStr}\,f\,f)\,f = (A \times_S A) \times_S A$ (invertible meaning locally on the source isomorphic to the structure sheaf) together with a trivialisation of its pullback along the section cut out by the unit point of the product group law $L \times L$. Assume three face hypotheses $h_1, h_2, h_3$: the pullbacks of $M.L$ along the morphisms $A \times_S A \to (A \times_S A) \times_S A$ given on points by $(x,y) \mapsto ((e,x),y)$, $(x,y) \mapsto ((x,e),y)$ and $(x,y) \mapsto ((x,y),e)$, where $e$ denotes the unit section of $L$, are each locally isomorphic over the base to the unit module, in the sense that every point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ over which the two modules become isomorphic after restriction to the preimage of $U$. The conclusion asserts the existence of a noetherian commutative ring $S_0$, a scheme $A_0$ with a morphism $f_0 : A_0 \to \operatorname{Spec} S_0$, a relative group law $L_0$ on $f_0$, the same bundle of properties for $f_0$, and a rigidified line bundle $M_0$ on $(A_0 \times_{S_0} A_0) \times_{S_0} A_0$ rigidified along the unit of $L_0 \times L_0$, such that the three corresponding face conditions hold over $S_0$ and, moreover, if $M_0.L$ is isomorphic to the module of the trivial rigidified bundle over $S_0$ then $M.L$ is isomorphic to the module of the trivial rigidified bundle over $S$.
--
--   This is the noetherian reduction step for the theorem of the cube in the rigidified relative Picard setting: it replaces an arbitrary affine base by a noetherian one while keeping the group law, the rigidified bundle and the triviality of its three faces, and transporting triviality back. It is used by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces), where the cube theorem is then proved over the noetherian model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    ∃ (S₀ : Type) (_ : CommRing S₀) (_ : IsNoetherianRing S₀) (A₀ : Scheme) (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀))
      (L₀ : RelativeGroupLaw S₀ f₀) (_ : AbelianSchemePropertyBundle S₀ f₀)
      (M₀ : RigidifiedLineBundle (prodStr f₀ f₀) ((L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀),
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (L₀.one (prodStr f₀ f₀)).1 (pullback.fst f₀ f₀) (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc, (L₀.one _).2]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst f₀ f₀) (L₀.one (prodStr f₀ f₀)).1 (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) (L₀.one (prodStr f₀ f₀)).1 (by rw [Category.id_comp, (L₀.one _).2]))).obj M₀.L) (𝟙_ _) ∧
      (Nonempty (M₀.L ≅ (RigidifiedLineBundle.unit (c := prodStr f₀ f₀) (ε := (L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀)))) f₀).L) →
        Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f).L)) := by sorry
