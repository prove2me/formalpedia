-- Prove2me | Theorems.Thm_AlgebraicGeometry_Etale_isIso_of_isSeparated_of_geometricallyConnected
-- name    : AlgebraicGeometry.Etale.isIso_of_isSeparated_of_geometricallyConnected
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T15:53:55.260791+00:00
-- url     : https://prove2.me/theorems/d21f83b1-9bcd-4401-aecf-7d9f9d5b0e10
-- title:
--   A separated etale morphism with geometrically connected fibres is an isomorphism
-- statement:
--   Let $f:X\to Y$ be a separated étale morphism of schemes. Suppose every geometric fibre is connected and nonempty. Then
--   $$f:X\overset{\sim}{\longrightarrow}Y.$$
--   No properness, noetherianness, or integrality hypothesis is needed. The empty-base case is included. In particular, a proper smooth family of relative dimension zero with geometrically connected fibres is isomorphic to its base.
--
--   This identifies the dimension-zero open family in the prepared Philippon boundary problem; the behaviour of its projective compactification across the remaining boundary is a separate assertion.
-- source:
--   Consequence of the diagonal criterion for separated and unramified morphisms and Stacks Project, Theorem 41.14.1, https://stacks.math.columbia.edu/tag/025G ; the final descent principle is Lemma 35.25.1, https://stacks.math.columbia.edu/tag/06NC . The diagonal is open and closed and is a section of a morphism with connected fibres, so it is surjective. This is a derived criterion, not a verbatim numbered statement. The argument applies to arbitrary schemes and includes empty bases.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.Etale.isIso_of_isSeparated_of_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f]
    [GeometricallyConnected f] : IsIso f := by sorry
