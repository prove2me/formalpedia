-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle
-- name    : AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c8e4f90c-ab24-5052-bc33-b2b12880cb2d
-- title:
--   2-torsion characters from [2]^*-trivial rigidified line bundles
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\operatorname{Hom}_{\operatorname{Spec} S}(T, A)$, natural in $T$), assume $L$ is commutative, assume `AbelianSchemePropertyBundle S f` ($f$ smooth and proper with connected fibres and admitting a relative group law), assume that the structure morphism of the kernel of multiplication by $2$, namely the second projection of the pullback of $L$'s doubling endomorphism $[2] =$ `L.schemeNsmul 2` against the unit section, is finite, flat and locally of finite presentation, and assume $[2] : A \to A$ is affine, flat and surjective. Then there is a rule $\Phi$ assigning, to every commutative ring $R$, every $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$ and every rigidified line bundle $N$ on $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ (an invertible module $N.L$ together with a trivialisation along the section induced by the identity $L.\mathrm{one}$), a $2$-torsion character $\Phi_{R,\iota}(N)$, i.e. a function sending each $T$-point $x$ of $A$ over $\kappa \circ \iota$ with $2x = 0$ to a unit of $T$, multiplicative in $x$ and compatible with ring maps $T \to T'$, such that, writing $\mathrm{Adm}(N)$ for the condition that $[2]_{A_R}^* (N.L)$ — pullback along `(L.baseChange ι).schemeNsmul 2` — is isomorphic to the monoidal unit: (i) $\Phi_{R,\iota}(N) = \Phi_{R,\iota}(N')$ whenever $N.L \cong N'.L$; (ii) for $\psi : \operatorname{Spec} R' \to \operatorname{Spec} R$ over $\operatorname{Spec} S$, $N$ with $\mathrm{Adm}(N)$, and $2$-torsion points $x'$ over $\kappa' \circ \iota'$ and $x$ over $(\kappa' \circ \psi) \circ \iota$ with the same underlying morphism, $\Phi_{R',\iota'}(N \text{ pulled back along } \psi)$ takes the same value at $x'$ as $\Phi_{R,\iota}(N)$ at $x$; (iii) every $2$-torsion character over $\iota$ equals $\Phi_{R,\iota}(N)$ for some $N$ with $\mathrm{Adm}(N)$; (iv) if $\mathrm{Adm}(N)$, $\mathrm{Adm}(N')$ and $\Phi_{R,\iota}(N) = \Phi_{R,\iota}(N')$ then $N.L \cong N'.L$; (v) if $\mathrm{Adm}(N)$, $\mathrm{Adm}(N')$ and $N''.L \cong N.L \otimes N'.L$, then the values of $\Phi_{R,\iota}(N'')$ are the products of those of $\Phi_{R,\iota}(N)$ and $\Phi_{R,\iota}(N')$; and (vi) if $N.L$ is isomorphic to the monoidal unit then all values of $\Phi_{R,\iota}(N)$ are $1$.
--
--   This is the descent statement along multiplication by $2$ on an abelian scheme: rigidified line bundles whose pullback under $[2]$ is trivial are classified, up to isomorphism and compatibly with base change and tensor product, by characters of the $2$-torsion, in the style of the theory of the dual abelian scheme. It is used in the formalisation to treat the symmetric case $N \otimes N$ and to produce local isomorphisms on the base from $[2]^*$-trivial bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle.lean

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

theorem AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2)) :
    ∃ Φ : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι,

      let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
          RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
        fun R _ ι N =>
          Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)

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
