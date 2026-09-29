-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic_of_locallyQuasiFinite_primePow
-- name    : AlgebraicGeometry.RelPicard.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic_of_locallyQuasiFinite_primePow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/8a5d62d9-c6a6-59a7-9876-3100c8a1ae26
-- title:
--   Flatness and surjectivity of [n] on a relative Pic⁰ over ℤ
-- statement:
--   Fix a prime $p$ and a scheme $C$ with a structure morphism $c : C \to \operatorname{Spec}\mathbf{Z}$, together with $\varepsilon$, a morphism $\operatorname{Spec}\mathbf{Z} \to C$ whose composite with $c$ is the identity. Let $D$ consist of a scheme $P$, a morphism `D.toBase` $: P \to \operatorname{Spec}\mathbf{Z}$ and a section `D.zeroSection` of it. Assume `hD`: $D$ represents the subfunctor `algEquivZeroCut c ε` of the rigidified relative Picard functor of $(C,\varepsilon)$, i.e. there is a rigidified line bundle (the Poincaré bundle) on the base change of $C$ along `D.toBase` which is fibrewise algebraically equivalent to zero over every algebraically closed point, such that for every $t : T \to \operatorname{Spec}\mathbf{Z}$ and every rigidified line bundle $M$ on $C_T$ with the same fibrewise property there is a unique $T$-point $g$ of $P$ over $t$ with the pullback of the Poincaré bundle along $g$ isomorphic to $M$, and such that the pullback along the zero section is the unit bundle. Assume further that `D.toBase` is smooth and geometrically connected. Write $L$ for the relative group law on `D.toBase` obtained from the representability `hD` for the group-theoretic refinement `algEquivZeroGroupCut c ε` of this cut (the same fibrewise condition, closed under tensor products and inverses). Hypothesis `hA` asks that for every point $s$ of $\operatorname{Spec}\mathbf{Z}$ with ideal $(p)$ and every $k \ge 1$, multiplication by $p^k$ on the fibre of $L$ over $s$ (a relative group law over the residue field at $s$) is locally quasi-finite; hypothesis `hB` asks that for every prime $\ell \ne p$ and every $k \ge 1$, multiplication by $\ell^k$ on the base change of $L$ along $\operatorname{Spec}$ of $\mathbf{Z} \to \mathbf{Z}_{(\ell)}$ (the subring of rationals with denominator coprime to $\ell$) is locally quasi-finite. The conclusion is that for every $n > 0$ the endomorphism `schemeNsmul` $n$ of $P$, namely $n$-fold multiplication under $L$ applied to the identity point, is flat, surjective and locally quasi-finite.
--
--   This is the statement that $[n]$ is an isogeny-like map — flat, surjective and locally quasi-finite — on the relative $\mathrm{Pic}^0$ of a pointed curve over $\mathbf{Z}$, phrased for the representing scheme of the algebraic-equivalence-to-zero cut of the rigidified relative Picard functor rather than for an abstract smooth relative group law. It is used in the construction of the good Néron identity component attached to a model of the modular curve, via [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic_of_locallyQuasiFinite_primePow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic_of_locallyQuasiFinite_primePow
    (p : ℕ) [Fact p.Prime] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase)
    (hA : ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).fibre s).schemeNsmul
        (p ^ k)))
    (hB : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).schemeNsmul (ℓ ^ k))) :
    (∀ n : ℕ, 0 < n →
      Flat ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      Surjective ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      LocallyQuasiFinite ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) := by sorry
