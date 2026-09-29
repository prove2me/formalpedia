-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/13d28093-e6cf-5404-b25d-fa882b44560a
-- title:
--   Theta-cube triviality along (x,x,-x) and [2]^*N
-- statement:
--   Fix a commutative ring $S$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} S$, together with a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} S$, satisfying associativity, the unit laws, left inverse and naturality in $T$), a hypothesis `hc` that $L$ is commutative, and a bundle `hA` of properties asserting that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ is connected, and that $f$ carries some relative group law. Let $R$ be a commutative ring, $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$, write $B := A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ with structure morphism $g :=$ `pullback.snd f ι` and $L' :=$ `L.baseChange ι` the induced group law on $g$, with addition `addMor` and inversion $[-1] :=$ `negMor`. Let $N$ be a line bundle on $B$ rigidified along the unit section $L.\mathrm{one}(\mathrm{id})$: a module $N.L$ on $B$ that is invertible (each point has a neighbourhood on whose restriction it is isomorphic to the unit module) and whose pullback along the rigidifying section is isomorphic to the unit module on $\operatorname{Spec} R$. Write $\Lambda(N) := \mathrm{addMor}^*N.L \otimes (p_1^*(N.L)^\vee \otimes p_2^*(N.L)^\vee)$ on $B \times_R B$, the Mumford bundle, and let $\Theta(N)$ on $(B \times_R B)\times_R B$ be the pullback of $\Lambda(N)$ along $((x,y),z) \mapsto (x+y,z)$ tensored with the duals of its pullbacks along $((x,y),z)\mapsto(x,z)$ and $((x,y),z)\mapsto(y,z)$. The hypothesis is that the pullback of $\Theta(N)$ along the morphism $B \to (B\times_R B)\times_R B$, $x \mapsto ((x,x),[-1]x)$, admits an isomorphism to the unit object. The conclusion is that there is an isomorphism $[2]^*N.L \cong (N.L \otimes N.L \otimes N.L) \otimes [-1]^*N.L$, where $[2] :=$ `(L.baseChange ι).schemeNsmul 2` is the doubling morphism of $L'$ on $B$; both hypothesis and conclusion are stated as nonemptiness of the corresponding types of isomorphisms.
--
--   This is the theorem of the square for $n = 2$ on an abelian scheme, obtained by restricting the theta-cube associated with a rigidified line bundle to the diagonal-type section $x \mapsto ((x,x),-x)$. It feeds into [`AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified`](thm.html#AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_tensor_pullback_negMor_of_rigidified), which packages the same conclusion without the triviality hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_of_nonempty_pullback_thetaCube_iso_unit
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (h : Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.lift (𝟙 _) (𝟙 _) rfl) (negMor (pullback.snd f ι) (L.baseChange ι))
          (by rw [pullback.lift_fst_assoc, Category.id_comp, negMor_over]))).obj
        ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ addMor (pullback.snd f ι) (L.baseChange ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, addMor_over]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L) ⊗
      (Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)) ⊗
       Scheme.Modules.dual ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι) ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd (prodStr (pullback.snd f ι) (pullback.snd f ι)) (pullback.snd f ι))
          (by rw [Category.assoc, ← pullback.condition (f := (pullback.snd f ι)) (g := (pullback.snd f ι))]; exact pullback.condition))).obj (mumfordBundle (pullback.snd f ι) (L.baseChange ι) N.L)))) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅
      (N.L ⊗ N.L ⊗ N.L) ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) := by sorry
