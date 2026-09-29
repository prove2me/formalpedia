-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_bijOn_symmetric_tensor_self_rigidifiedLineBundle
-- name    : AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_symmetric_tensor_self_rigidifiedLineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/471527f5-5779-5ba2-abbb-86658d94fe35
-- title:
--   Symmetric square-trivial rigidified bundles as 2-torsion characters
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism equipped with a relative group law `L` (a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections over varying bases $t$), assumed commutative, with $f$ satisfying `AbelianSchemePropertyBundle` (smooth, proper, with connected fibres, and admitting a relative group law), and with the kernel scheme of multiplication by $2$, $\mathrm{schemeKerStr}\,2$, finite, flat and locally of finite presentation over $\operatorname{Spec} S$. The assertion is the existence of an operator $\Phi$ which, for each commutative ring $R$, each $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$ and each line bundle $N$ on the pullback $A\times_S\operatorname{Spec} R$ rigidified along the identity section, produces a $2$-torsion character $\Phi\,R\,\iota\,N$ over $\iota$ (units $\chi(x)\in T^{\times}$ attached to the $2$-torsion sections $x$ over all $R$-algebras $T$, multiplicative in $x$ and natural in $T$). Writing $\mathrm{Adm}(N)$ for the conjunction of the two conditions that the pullback of $N.L$ along the inversion morphism of the base-changed group law is isomorphic to $N.L$, and that $N.L\otimes N.L$ is isomorphic to the unit module, both only locally on the base in the sense of `LocIsoOnBase` (each point of $\operatorname{Spec} R$ has an open neighbourhood $U$ over whose preimage the two modules become isomorphic), the following six properties hold: (i) $\Phi\,R\,\iota\,N = \Phi\,R\,\iota\,N'$ whenever $N.L \cong N'.L$; (ii) naturality: given $\psi : \operatorname{Spec} R' \to \operatorname{Spec} R$ over $\operatorname{Spec} S$, an admissible $N$ over $\iota$, a ring $T$, $\kappa' : \operatorname{Spec} T \to \operatorname{Spec} R'$, and $2$-torsion sections $x'$ over $\kappa'\circ\iota'$ and $x$ over $(\kappa'\circ\psi)\circ\iota$ with the same underlying morphism, the character of the pulled-back bundle $N.\mathrm{pullbackAlong}\,\psi$ takes at $x'$ the value that $\Phi\,R\,\iota\,N$ takes at $x$; (iii) every $2$-torsion character over $\iota$ equals $\Phi\,R\,\iota\,N$ for some admissible $N$; (iv) two admissible bundles with the same character have isomorphic underlying modules; (v) if $N,N'$ are admissible and $N''.L \cong N.L\otimes N'.L$, then the values of $\Phi\,R\,\iota\,N''$ are the pointwise products of those of $\Phi\,R\,\iota\,N$ and $\Phi\,R\,\iota\,N'$; (vi) if $N.L$ is isomorphic to the unit module, all values of $\Phi\,R\,\iota\,N$ are $1$.
--
--   This is the Cartier-duality description, in the form needed here, of the group of symmetric rigidified line bundles of order dividing $2$ on an abelian scheme as the group of characters of its $2$-torsion, with admissibility expressed by the two symmetry and square-triviality conditions holding locally on the base (Mumford, Abelian Varieties §15). It is used in the construction of square roots of a canonical bundle over a local base, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_bijOn_symmetric_tensor_self_rigidifiedLineBundle.lean

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

theorem AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_symmetric_tensor_self_rigidifiedLineBundle
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2)) :
    ∃ Φ : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι,

      let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
          RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
        fun R _ ι N =>
          LocIsoOnBase (pullback.snd f ι)
              ((Scheme.Modules.pullback (negMor (pullback.snd f ι) (L.baseChange ι))).obj N.L) N.L ∧
          LocIsoOnBase (pullback.snd f ι) (N.L ⊗ N.L) (𝟙_ _)

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Nonempty (N.L ≅ N'.L) → Φ R ι N = Φ R ι N') ∧

      (∀ (R R' : Type) [CommRing R] [CommRing R'] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : SchemeHomOver ι' ι)
          (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι)
          (T : Type) [CommRing T] (κ' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
          (x' : SchemeHomOver (κ' ≫ ι') f) (hx' : L.IsTorsionPoint (κ' ≫ ι') 2 x')
          (x : SchemeHomOver ((κ' ≫ ψ.1) ≫ ι) f) (hx : L.IsTorsionPoint ((κ' ≫ ψ.1) ≫ ι) 2 x),
          Adm R ι N → x'.1 = x.1 →
            (Φ R' ι' (N.pullbackAlong ψ)).val T κ' x' hx' = (Φ R ι N).val T (κ' ≫ ψ.1) x hx) ∧

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (χ : L.TorsionCharacter 2 ι),
          ∃ N, Adm R ι N ∧ Φ R ι N = χ) ∧

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Adm R ι N → Adm R ι N' → Φ R ι N = Φ R ι N' →
          Nonempty (N.L ≅ N'.L)) ∧

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' N'' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Adm R ι N → Adm R ι N' →
          Nonempty (N''.L ≅ N.L ⊗ N'.L) →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x),
            (Φ R ι N'').val T κ x hx = (Φ R ι N).val T κ x hx * (Φ R ι N').val T κ x hx) ∧

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Nonempty (N.L ≅ 𝟙_ _) →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x),
            (Φ R ι N).val T κ x hx = 1) := by sorry
