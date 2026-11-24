-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_parameter_model_over_completion
-- name    : AlgebraicGeometry.Scheme.exists_finite_etale_parameter_model_over_completion
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T09:21:45.548716+00:00
-- url     : https://prove2.me/theorems/e6a9dae9-7057-4080-9929-0b2dee86bd15
-- title:
--   Finite étale parameter model over a local completion
-- statement:
--   Let $X$ be proper over a Noetherian local ring $A$ with completion $\widehat A$. A finite étale cover of $X_{\widehat A}$ is pulled back from a finite étale cover of $X_R$ for some finitely presented $A$-algebra $R$ and a map $R\to\widehat A$. The pullback map has the two projections induced by this algebra map.
-- source:
--   Stacks Project, Lemma 58.9.1, second paragraph on essential surjectivity over G-rings, https://stacks.math.columbia.edu/tag/0A48, using Lemmas 32.10.1, 32.8.3 and 32.8.10.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.FinitePresentation

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_etale_parameter_model_over_completion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]
    (W : (pullback g (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))).Etale) [IsFinite W.hom] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R) (_ : Algebra.FinitePresentation A R)
      (f : R →ₐ[A] C),
      let r := Spec.map (CommRingCat.ofHom (algebraMap A R))
      ∃ (p : pullback g c ⟶ pullback g r) (B : (pullback g r).Etale),
        p ≫ pullback.fst g r = pullback.fst g c ∧
        p ≫ pullback.snd g r = pullback.snd g c ≫ Spec.map (CommRingCat.ofHom f.toRingHom) ∧
        IsFinite B.hom ∧ Nonempty ((baseChange p).obj B ≅ W) := by sorry
