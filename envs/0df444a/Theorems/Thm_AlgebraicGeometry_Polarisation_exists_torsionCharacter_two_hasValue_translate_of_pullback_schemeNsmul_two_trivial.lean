-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
-- name    : AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/09d2c161-d90b-5334-b8d2-92c68128e9e1
-- title:
--   Existence of the 2-torsion descent character Φ
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of points of $A$ over $\operatorname{Spec}S$-schemes $t\colon T\to\operatorname{Spec}S$. Assume $L$ is commutative; assume the bundle of properties `AbelianSchemePropertyBundle` for $f$ (smooth, proper, connected fibres, and a relative group law exists); assume the structure morphism of $\ker[2]$, namely the second projection of the fibre product of $[2]=$`L.schemeNsmul 2` and the unit section, is finite, flat and locally of finite presentation; and assume $[2]$ is an affine, flat and surjective morphism. The conclusion asserts the existence of a rule $\Phi$ attaching to every commutative ring $R$, every $\iota\colon\operatorname{Spec}R\to\operatorname{Spec}S$ and every rigidified line bundle $N$ on $A_R=A\times_{\operatorname{Spec}S}\operatorname{Spec}R$ (an invertible module $N.L$ together with a trivialisation of its restriction along the rigidifying section at the identity) a $2$-torsion character $\Phi(R,\iota,N)$ in the sense of `TorsionCharacter`: a family of units $\Phi(R,\iota,N).\mathrm{val}\,T\,\kappa\,x\in T^\times$, indexed by rings $T$, morphisms $\kappa\colon\operatorname{Spec}T\to\operatorname{Spec}R$ and points $x$ of $A$ over $\kappa\circ\iota$ with $2x$ the identity, multiplicative in $x$ and natural in ring homomorphisms. Writing $\mathrm{Adm}(R,\iota,N)$ for the condition that the pullback of $N.L$ along $[2]$ of the base-changed group law is isomorphic to the unit module, the four asserted clauses are: (i) for all such $R,\iota,N$ with $\mathrm{Adm}(R,\iota,N)$, all $T$, $\kappa$, all $2$-torsion $x$ over $\kappa\circ\iota$, any proof $hTq$ that translation by $x$ on $A_T$ composed with $[2]_T$ equals $[2]_T$, and any isomorphism $\beta$ from $[2]_T^{*}$ of the pullback of $N$ along $\kappa$ to $[2]_T^{*}$ of the unit, the discrepancy $\beta^{-1}$ followed by the translate of $\beta$ acts on sections as multiplication by the image of $\Phi(R,\iota,N).\mathrm{val}\,T\,\kappa\,x$ in $T$, relative to the structure morphism $A_T\to\operatorname{Spec}T$, and this element of $T$ is the unique one with that property; (ii) $\Phi(R,\iota,N)=\Phi(R,\iota,N')$ whenever $N.L\cong N'.L$; (iii) if $\mathrm{Adm}$ holds for $N$ and $N'$ and $N''.L\cong N.L\otimes N'.L$, then the values of $\Phi(R,\iota,N'')$ are the products of those of $\Phi(R,\iota,N)$ and $\Phi(R,\iota,N')$; (iv) if $N.L$ is isomorphic to the unit module then all values of $\Phi(R,\iota,N)$ equal $1$.
--
--   This is the construction of the character $\Phi$ underlying the identification of the kernel of $[2]^{*}$ on the relative Picard functor with the dual of $A[2]$, in the style of Mumford's treatment of the duality between an isogeny and its dual; the descent discrepancy of a trivialisation of $[2]^{*}N$ at translation by a $2$-torsion point is the scalar recorded by $\Phi$. It is used by [`AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle`](thm.html#AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle), where naturality, injectivity and surjectivity of this assignment are added.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter

theorem AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial
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
          (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Adm R ι N →
          ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
            (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
            (hTq : (L.baseChange (κ ≫ ι)).translate
                (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                  ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
              (L.baseChange (κ ≫ ι)).schemeNsmul 2)
            (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
                  (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
                (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)),
            HasValue (pullback.snd f (κ ≫ ι)) hTq β (((Φ R ι N).val T κ x hx : Tˣ) : T) ∧
            ∀ c : T, HasValue (pullback.snd f (κ ≫ ι)) hTq β c → c = (((Φ R ι N).val T κ x hx : Tˣ) : T)) ∧

      (∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
          (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι), Nonempty (N.L ≅ N'.L) → Φ R ι N = Φ R ι N') ∧

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
