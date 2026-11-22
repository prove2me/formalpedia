-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite
-- name    : AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T15:50:59.123983+00:00
-- url     : https://prove2.me/theorems/69e58982-bec4-4878-a995-7c7a2d8a4659
-- title:
--   Finite schemes over strictly henselian local rings
-- statement:
--   Let $R$ be a strictly henselian local ring. If $Y \to \operatorname{Spec} R$ is finite, then $Y$ is a finite disjoint union of spectra of strictly henselian local rings. Each component inclusion into $Y$ is a closed immersion.
-- source:
--   Stacks Project, Proposition 59.55.2, https://stacks.math.columbia.edu/tag/03QP.

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsFinite p] :
    ∃ (ι : Type u) (_ : Fintype ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
      (h : ∀ i, HenselianLocalRing (T i)),
      (∀ i, let _ := h i; IsSepClosed (IsLocalRing.ResidueField (T i))) ∧
        ∃ (c : (∐ fun i ↦ Spec (.of (T i))) ≅ Y),
          ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (T j))) i ≫ c.hom) := by sorry
