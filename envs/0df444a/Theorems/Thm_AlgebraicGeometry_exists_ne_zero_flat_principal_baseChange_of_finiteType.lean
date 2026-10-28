-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ne_zero_flat_principal_baseChange_of_finiteType
-- name    : AlgebraicGeometry.exists_ne_zero_flat_principal_baseChange_of_finiteType
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T16:55:45.626491+00:00
-- url     : https://prove2.me/theorems/535b0e9d-8abd-4406-a5b3-04bbf77128a4
-- title:
--   Generic flatness after actual principal base change over a noetherian domain
-- statement:
--   Let $A$ be a commutative noetherian integral domain, let $X$ be a quasi-compact scheme, and let $f:X\to\operatorname{Spec}A$ be locally of finite type. There is a nonzero $a\in A$ such that the actual base-changed morphism
--   $$X\times_{\operatorname{Spec}A}\operatorname{Spec}A[1/a]
--      \longrightarrow\operatorname{Spec}A[1/a]$$
--   is flat.
--
--   The statement is universe polymorphic and imposes no reducedness, irreducibility or separatedness hypothesis on $X$. It is the scheme form of generic flatness, retaining a principal localization of the prescribed base rather than an unspecified isomorphic model. It supplies a flat target family before spreading generic covering maps in the Philippon alteration branch.
-- source:
--   Scheme generic flatness for the Philippon alteration branch https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Uses the Proved algebraic generic-flatness theorem https://prove2.me/theorems/41f36edb-396e-5ac8-8c58-8a06150d9dd5 . The proof transports localized-ring flatness to scheme restrictions, passes to a finite affine cover and a common dense base open, and retains actual principal base change. Complements the accepted covering-family theorem https://prove2.me/theorems/604920e5-4cba-4868-8bdc-68398a8edcb3 . Semistable reduction and global alteration are separate.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_ne_zero_flat_principal_baseChange_of_finiteType
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    ∃ a : A, a ≠ 0 ∧
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away a))))) := by sorry
