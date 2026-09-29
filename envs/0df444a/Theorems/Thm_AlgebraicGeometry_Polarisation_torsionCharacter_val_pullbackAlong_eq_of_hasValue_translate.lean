-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
-- name    : AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/f064886a-5c16-5f9b-83f6-af376f356e82
-- title:
--   Naturality of the 2-torsion descent character in the test ring
-- statement:
--   Fix a commutative ring $S$, a scheme $A$ and a morphism $f\colon A\to\operatorname{Spec} S$, a relative group law $L$ on $f$ (functorial group structures on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of points over each base morphism $t$, natural in $T$), assumed commutative; assume the bundle of properties $\mathrm{AbelianSchemePropertyBundle}$ for $f$ (smooth, proper, connected fibres, and existence of a relative group law), that the kernel scheme of multiplication by $2$ is finite, flat and locally of finite presentation over $\operatorname{Spec} S$, and that $L.\mathrm{schemeNsmul}\,2$, the morphism $[2]\colon A\to A$, is an affine, flat and surjective morphism. Two auxiliary predicates are introduced, indexed by a commutative ring $R$ and a morphism $\iota\colon\operatorname{Spec} R\to\operatorname{Spec} S$: for a rigidified line bundle $N$ on $A\times_S\operatorname{Spec} R$ (an invertible module with a trivialisation along the unit section), $\mathrm{Adm}$ says that the pullback of $N.L$ along the base-changed $[2]$ is isomorphic to the monoidal unit; and $\mathrm{IsCharOf}\;R\;\iota\;N\;\chi$, for a $2$-torsion character $\chi$ at $\iota$, says that for every commutative ring $T$, every $\kappa\colon\operatorname{Spec} T\to\operatorname{Spec} R$, every point $x$ of $A$ over $\kappa\circ\iota$ killed by $2$, every proof that translation by the corresponding point of the base change $A_T$ commutes with $[2]$ there, and every isomorphism $\beta$ between the $[2]$-pullback of the $\kappa$-pullback of $N$ and the $[2]$-pullback of the unit, the discrepancy automorphism $\beta^{-1}$ followed by the translate of $\beta$ is multiplication by the image of $\chi.\mathrm{val}\,T\,\kappa\,x \in T^{\times}$ under the structure morphism $A_T\to\operatorname{Spec} T$. The assertion is: for commutative rings $R, R'$, morphisms $\iota\colon\operatorname{Spec} R\to\operatorname{Spec} S$ and $\iota'\colon\operatorname{Spec} R'\to\operatorname{Spec} S$, a morphism $\psi\colon\operatorname{Spec} R'\to\operatorname{Spec} R$ with $\psi$ followed by $\iota$ equal to $\iota'$, a rigidified line bundle $N$ at $\iota$ and $2$-torsion characters $\chi$ at $\iota$ and $\chi'$ at $\iota'$, if $N$ satisfies $\mathrm{Adm}$, if $\chi$ is a character of $N$ and $\chi'$ is a character of the pullback of $N$ along $\psi$, then for every commutative ring $T$, every $\kappa'\colon\operatorname{Spec} T\to\operatorname{Spec} R'$, every $2$-torsion point $x'$ over $\kappa'\circ\iota'$ and every $2$-torsion point $x$ over $\iota\circ\psi\circ\kappa'$ whose underlying morphisms $\operatorname{Spec} T\to A$ agree, one has the equality of units $\chi'.\mathrm{val}\,T\,\kappa'\,x' = \chi.\mathrm{val}\,T\,(\kappa'\text{ followed by }\psi)\,x$.
--
--   This is the compatibility of the character attached to a line bundle trivialised by $[2]$ with change of the affine test base: the value at a $2$-torsion point depends only on the point of $A$, not on whether it is regarded over $\operatorname{Spec} R'$ or over $\operatorname{Spec} R$. It is used in the construction of the $2$-torsion descent character establishing the bijection between characters and rigidified line bundles whose $[2]$-pullback is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate.lean

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

theorem AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2)) :
    let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
      fun R _ ι N =>
        Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)
    let IsCharOf : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι → Prop :=
      fun R _ ι N χ =>
        ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
          (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
          (hTq : (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
            (L.baseChange (κ ≫ ι)).schemeNsmul 2)
          (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
                (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
              (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)),
          HasValue (pullback.snd f (κ ≫ ι)) hTq β ((χ.val T κ x hx : Tˣ) : T)
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
      (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : SchemeHomOver ι' ι)
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (χ : L.TorsionCharacter 2 ι) (χ' : L.TorsionCharacter 2 ι'),
      Adm R ι N → IsCharOf R ι N χ → IsCharOf R' ι' (N.pullbackAlong ψ) χ' →
      ∀ (T : Type) [CommRing T] (κ' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
        (x' : SchemeHomOver (κ' ≫ ι') f) (hx' : L.IsTorsionPoint (κ' ≫ ι') 2 x')
        (x : SchemeHomOver ((κ' ≫ ψ.1) ≫ ι) f) (hx : L.IsTorsionPoint ((κ' ≫ ψ.1) ≫ ι) 2 x),
        x'.1 = x.1 → χ'.val T κ' x' hx' = χ.val T (κ' ≫ ψ.1) x hx := by sorry
