-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_appTop_eq_idempotent_closed_fiber_of_isProper
-- name    : AlgebraicGeometry.Scheme.exists_appTop_eq_idempotent_closed_fiber_of_isProper
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T20:32:18.928802+00:00
-- url     : https://prove2.me/theorems/e053d449-a194-4e1e-aa75-d99db75c4dff
-- title:
--   Lift a global idempotent from the closed fiber of a proper scheme
-- statement:
--   Let $A$ be a local ring and $X$ a proper scheme over $\operatorname{Spec}(A)$. Every idempotent of $\Gamma(X_0,\mathcal O_{X_0})$ lies in the image of $\Gamma(X,\mathcal O_X) \to \Gamma(X_0,\mathcal O_{X_0})$, where $X_0$ is the closed fiber.
-- source:
--   Stacks Project, Lemma 36.32.7, https://stacks.math.columbia.edu/tag/0G7X.

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.Scheme.exists_appTop_eq_idempotent_closed_fiber_of_isProper    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (e : Γ(pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f, ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(X, ⊤),
      (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f).appTop.hom a = e := by sorry
