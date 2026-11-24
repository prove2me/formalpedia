-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_approximable_henselian_model_of_finite_etale_closed_fiber
-- name    : AlgebraicGeometry.Scheme.exists_approximable_henselian_model_of_finite_etale_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T09:20:06.066946+00:00
-- url     : https://prove2.me/theorems/801826be-0416-460b-a8e6-8d6c2fc2c3e2
-- title:
--   Henselian Noetherian approximation of a proper scheme and its closed-fiber cover
-- statement:
--   A proper scheme over a henselian local ring and a finite étale cover of its closed fiber descend to a proper scheme and a finite étale closed-fiber cover over a Noetherian henselian local ring. The approximating local ring can be chosen to satisfy Artin approximation modulo its maximal ideal for solutions of finite polynomial systems in its completion.
-- source:
--   Stacks Project, Lemma 58.9.1, general case, https://stacks.math.columbia.edu/tag/0A48, and Theorem 16.13.1, https://stacks.math.columbia.edu/tag/07QY.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.FinitePresentation

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
universe u

theorem AlgebraicGeometry.Scheme.exists_approximable_henselian_model_of_finite_etale_closed_fiber
    (A : Type u) [CommRing A] [HenselianLocalRing A] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (_ : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g)
    (V : T.Etale) [IsFinite V.hom] :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (X : Scheme.{u}) (g₀ : X ⟶ Spec (.of R)) (_ : IsProper g₀)
      (v : Y ⟶ X),
      let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
      let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
      ∃ (z : T ⟶ pullback r g₀) (B : (pullback r g₀).Etale),
        IsPullback g v (Spec.map (CommRingCat.ofHom a)) g₀ ∧
        IsPullback s z (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map a))) (pullback.fst r g₀) ∧
        j ≫ v = z ≫ pullback.snd r g₀ ∧
        IsFinite B.hom ∧ Nonempty ((baseChange z).obj B ≅ V) ∧
        (∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x' : Fin n → C),
          (∀ k, MvPolynomial.aeval x' (P k) = 0) →
          ∃ x : Fin n → R, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
            ∀ k, IsLocalRing.residue C (x' k) = IsLocalRing.ResidueField.map (algebraMap R C)
              (IsLocalRing.residue R (x k))) := by sorry
