-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2bade879-5999-54aa-abc5-c70ef412f753
-- title:
--   Rigidified line bundles with the same descent character agree
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ (functorial group structures on the sets of sections of $f$ over schemes over $\operatorname{Spec} S$, natural in the base) which is commutative, and assume the property bundle for $f$: $f$ is smooth, proper, has connected fibres, and admits a relative group law. Assume further that the structure morphism to $\operatorname{Spec} S$ of the kernel of doubling — the second projection of the fibre product of $[2] =$ `L.schemeNsmul 2`$\,: A \to A$ with the unit section — is finite, flat and locally of finite presentation, and that $[2]$ itself is an affine morphism, flat and surjective. For a commutative ring $R$ and $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$, consider rigidified line bundles $N$ on $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$, i.e. invertible modules $N.L$ together with a trivialisation of their restriction along the section cut out by the unit. Call $N$ admissible when the pullback of $N.L$ along the doubling endomorphism of the base-changed group law is isomorphic to the monoidal unit. Given a $2$-torsion character $\chi$ over $\iota$ (units $\chi(x) \in T^\times$ attached to $2$-torsion sections $x$ of $f$ over $\operatorname{Spec} T \to \operatorname{Spec} R \to \operatorname{Spec} S$, multiplicative in $x$ and natural in $T$), say that $N$ has character $\chi$ when for every commutative ring $T$, every $\kappa : \operatorname{Spec} T \to \operatorname{Spec} R$, every section $x$ of $f$ over $\kappa \circ \iota$ with $2x$ the unit, every witness that translation by the corresponding $T$-point followed by $[2]_T$ equals $[2]_T$, and every isomorphism $\beta$ from $[2]_T^{*}$ of the pullback of $N.L$ to $[2]_T^{*}$ of the unit, the discrepancy $\beta^{-1}$ followed by the translate of $\beta$ acts on sections as multiplication by the scalar $\chi(x)$ pulled back from $\operatorname{Spec} T$ along the projection $A_T \to \operatorname{Spec} T$. The conclusion: for every such $R$, $\iota$, every pair $N, N'$ of rigidified line bundles and every $2$-torsion character $\chi$ over $\iota$, if $N$ and $N'$ are admissible and both have character $\chi$, then the modules $N.L$ and $N'.L$ on $A_R$ are isomorphic (no compatibility with the rigidifications being asserted).
--
--   This is the injectivity half of the classification of line bundles on an abelian scheme that become trivial after pullback by $[2]$ in terms of characters of the $2$-torsion subgroup scheme, in the style of Mumford's descent along $[2]$. It is used in the construction of the bijection between such rigidified line bundles and $2$-torsion characters, [`AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle`](thm.html#AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_bijOn_pullback_schemeNsmul_two_trivial_rigidifiedLineBundle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_iso_of_hasValue_translate_eq_of_pullback_schemeNsmul_two_trivial
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
    ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
      (N N' : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (χ : L.TorsionCharacter 2 ι),
      Adm R ι N → Adm R ι N' → IsCharOf R ι N χ → IsCharOf R ι N' χ → Nonempty (N.L ≅ N'.L) := by sorry
