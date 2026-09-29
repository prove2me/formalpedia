-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_unit_of_locIsoOnBase_negMor_of_locIsoOnBase_tensor_self
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_unit_of_locIsoOnBase_negMor_of_locIsoOnBase_tensor_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c647c93d-5825-56a2-9f8c-5fb1fe9bc745
-- title:
--   Local symmetry and N^{⊗ 2}≅𝒪 force [2]^*N≅𝒪
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, natural in $T$; assume $L$ is commutative, and that $f$ carries the property bundle asserting that $f$ is smooth and proper with connected fibres and admits a relative group law. It is further assumed that the structure morphism $\ker[2] \to \operatorname{Spec} S$, realised as the second projection of the pullback of the multiplication-by-$2$ endomorphism $L.\mathrm{schemeNsmul}\,2$ against the unit section, is finite, flat and locally of finite presentation. Let $R$ be a commutative ring, $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$, write $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ with projection $p : A_R \to \operatorname{Spec} R$, and let $N$ be a rigidified line bundle: an invertible module $N.L$ on $A_R$ (locally isomorphic to the unit) together with a trivialisation of its pullback along the section of $p$ induced by the unit of $L$. Suppose that $[-1]^*N.L$ and $N.L$ are isomorphic locally on the base, and likewise $N.L \otimes N.L$ and the unit — that is, every point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage in $A_R$ the two modules become isomorphic, where $[-1]$ is the inversion endomorphism of $A_R$ for the base-changed group law. Then the pullback of $N.L$ along the multiplication-by-$2$ endomorphism of $A_R$ is isomorphic, globally on $A_R$, to the unit module.
--
--   This is the rigidity step in the construction of polarisations: a symmetric line bundle which is $2$-torsion locally on the base is killed by $[2]^*$ globally, as in the theory of the theorem of the square for abelian schemes. It supplies one implication of the equivalence [`AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit`](thm.html#AlgebraicGeometry.Polarisation.locIsoOnBase_negMor_and_tensor_self_iff_nonempty_pullback_schemeNsmul_two_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_two_iso_unit_of_locIsoOnBase_negMor_of_locIsoOnBase_tensor_self.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_two_iso_unit_of_locIsoOnBase_negMor_of_locIsoOnBase_tensor_self
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
    (hsym : LocIsoOnBase (pullback.snd f ι)
          ((Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) N.L)
    (hsq : LocIsoOnBase (pullback.snd f ι) (N.L ⊗ N.L) (𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _) := by sorry
