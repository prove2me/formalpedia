-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/d7f8aea4-a9e8-5e78-9232-62c96bf0494c
-- title:
--   Symmetric and locally square-trivial iff [2]^*N is trivial
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$ over $S$: a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws and naturality in the test scheme) on the sets of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for morphisms $t : T \to \operatorname{Spec} S$. Assume $L$ is commutative; assume $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists; and assume that the structure morphism to $\operatorname{Spec} S$ of the kernel of multiplication by $2$ — the second projection of the fibre product of `L.schemeNsmul 2` with the unit section — is finite, flat and locally of finite presentation. The assertion is then: for every commutative ring $R$, every morphism $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$, and every rigidified line bundle $N$ for $f$ along the unit section over $\iota$ — that is, a module $N.L$ on $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ which is invertible (each point has an open neighbourhood on which the restriction of $N.L$ is isomorphic to the unit module) together with an isomorphism between the pullback of $N.L$ along the section `rigSection` determined by the unit point and the unit module on $\operatorname{Spec} R$ — the conjunction of the two conditions: (i) the pullback of $N.L$ along the inversion endomorphism `negMor` of the base-changed group law `L.baseChange ι` is isomorphic to $N.L$ locally on the base, and (ii) $N.L \otimes N.L$ is isomorphic to the monoidal unit locally on the base, where 'locally on the base' means that every point $s$ of $\operatorname{Spec} R$ has an open neighbourhood $U$ such that the restrictions of the two modules to the preimage of $U$ under $\operatorname{pr}_2 : A \times_{\operatorname{Spec} S} \operatorname{Spec} R \to \operatorname{Spec} R$ are isomorphic, holds if and only if the pullback of $N.L$ along the doubling endomorphism `schemeNsmul 2` of `L.baseChange ι` is isomorphic, globally, to the monoidal unit.
--
--   This is the relative form, over a possibly non-reduced affine base, of the characterisation of those rigidified line bundles on an abelian scheme that are symmetric and of order dividing $2$ locally on the base as exactly those annihilated by pullback along multiplication by $2$; it rests on the theorem of the square. It is used in the construction of the bijection onto $2$-torsion characters, `exists_torsionCharacter_two_bijOn_symmetric_tensor_self_rigidifiedLineBundle`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TorsionCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2)) :
    ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι),
      (LocIsoOnBase (pullback.snd f ι)
          ((Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) N.L ∧
        LocIsoOnBase (pullback.snd f ι) (N.L ⊗ N.L) (𝟙_ _)) ↔
      Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _) := by sorry
