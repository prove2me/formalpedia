-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
-- name    : AlgebraicGeometry.Polarisation.exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/312f0394-7c64-5cd5-9d76-53baa1f8a7b0
-- title:
--   Descent function over [2] realising a 2-torsion character
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over arbitrary $t : T \to \operatorname{Spec} S$, compatible with composition in $T$; assume $L$ is commutative, that $f$ is smooth, proper, with connected fibres and admits a relative group law, that the structure morphism of the kernel of multiplication by $2$ (the second projection of the fibre product of `L.schemeNsmul 2` with the unit section) is finite, flat and locally of finite presentation, and that the endomorphism `L.schemeNsmul 2` of $A$ is affine, flat and surjective. Let $R$ be a commutative ring, $\iota : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $\chi$ be a $2$-torsion character of $L$ along $\iota$: a rule assigning to every commutative ring $T$, every $\kappa : \operatorname{Spec} T \to \operatorname{Spec} R$ and every point $x$ of $A$ over $\kappa \circ \iota$ killed by $2$ a unit of $T$, multiplicatively in $x$ and naturally in $T$. Let $P, P_3$ be schemes, $p_1, p_2 : P \to A_R := A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ morphisms with $[2]_{A_R} \circ p_1 = [2]_{A_R} \circ p_2$ (multiplication by $2$ for the base-changed law), let $\delta : A_R \to P$ satisfy $p_1 \circ \delta = p_2 \circ \delta = \mathrm{id}$, and let $a, b, c : P_3 \to P$ satisfy $p_2 \circ a = p_1 \circ b$, $p_1 \circ c = p_1 \circ a$ and $p_2 \circ c = p_2 \circ b$. Then there is a global section $u$ of the structure sheaf of $P$ with $\delta^{*}u = 1$ and $a^{*}u \cdot b^{*}u = c^{*}u$, such that for every commutative ring $T$, every $\kappa : \operatorname{Spec} T \to \operatorname{Spec} R$, every point $x$ of $A$ over $\kappa \circ \iota$ with $2x$ the unit point, and every $s : A_T \to P$ with $p_1 \circ s$ the base-change morphism $A_T \to A_R$ induced by $\kappa$ and $p_2 \circ s$ that morphism precomposed with translation by $x$ for the law base changed to $T$, one has $s^{*}u = \pi^{*}(\chi(x))$, where $\pi : A_T \to \operatorname{Spec} T$ is the projection and $\chi(x) \in T^{\times}$ is viewed as a global function via the canonical isomorphism $\Gamma(\operatorname{Spec} T) \cong T$. No cartesianness is assumed of the square formed by $p_1, p_2$ and $[2]_{A_R}$ beyond the listed identities.
--
--   The section $u$ is the multiplicative descent datum (a cocycle-type function on a square over multiplication by $2$) that encodes the $2$-torsion character $\chi$, normalised along $\delta$ and evaluating to the constant $\chi(x)$ on the graph of translation by a $2$-torsion point $x$. It is the abelian-scheme input to the surjectivity half of the comparison between $2$-torsion characters and rigidified line bundles trivialised by pullback along $[2]$, used in [`AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val.lean

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

theorem AlgebraicGeometry.Polarisation.exists_appTop_eq_one_and_mul_eq_and_appTop_eq_torsionCharacter_two_val
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2))
    (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (χ : L.TorsionCharacter 2 ι)
    {P P₃ : Scheme} (p₁ p₂ : P ⟶ pullback f ι)
    (hp : p₁ ≫ (L.baseChange ι).schemeNsmul 2 = p₂ ≫ (L.baseChange ι).schemeNsmul 2)
    (δ : pullback f ι ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 _) (hδ₂ : δ ≫ p₂ = 𝟙 _)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂) :
    ∃ u : Γ(P, ⊤), δ.appTop u = 1 ∧ a.appTop u * b.appTop u = c.appTop u ∧
      ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
        (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
        (s : pullback f (κ ≫ ι) ⟶ P)
        (hs₁ : s ≫ p₁ = RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι))
        (hs₂ : s ≫ p₂ = (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
            RelPicard.baseChangeSnd f (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)),
        s.appTop u =
          (pullback.snd f (κ ≫ ι)).appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ((χ.val T κ x hx : Tˣ) : T)) := by sorry
