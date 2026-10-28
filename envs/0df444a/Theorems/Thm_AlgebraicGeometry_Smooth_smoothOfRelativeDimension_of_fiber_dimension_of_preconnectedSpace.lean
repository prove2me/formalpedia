-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_of_fiber_dimension_of_preconnectedSpace
-- name    : AlgebraicGeometry.Smooth.smoothOfRelativeDimension_of_fiber_dimension_of_preconnectedSpace
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T03:43:40.223564+00:00
-- url     : https://prove2.me/theorems/3e4c40e7-2f32-44ac-8de3-8ba6fdd920ee
-- title:
--   One nonempty fibre determines the relative dimension of a smooth preconnected source
-- statement:
--   Let $f:X\to Y$ be a smooth morphism of schemes with preconnected source $X$. Let $y\in Y$ have nonempty actual scheme-theoretic fibre $X_y$, and let $d\geq0$ be an integer. If
--   $$\dim X_y=d,$$
--   then $f$ is smooth of relative dimension $d$ on the whole source.
--
--   The base is arbitrary. Neither properness nor surjectivity of $f$, integrality of $X$, or a chosen ground field is required. In particular an integral smooth proper family with an actual dimension-one generic fibre is a family of smooth relative-dimension-one curves.
-- source:
--   Combines the Proved fixed-relative-dimension theorem for smooth morphisms with preconnected source https://prove2.me/theorems/cb52222f-94d6-5f1e-a5ee-7cc3c2bb1459 with the Proved upper bound and closed-stalk dimension formulas over a field, https://prove2.me/theorems/de7870b0-9619-54d5-ade4-addae1c90a85 and https://prove2.me/theorems/2f95e3ba-1508-514d-b34d-dcab4cd48399 . This identifies the relative dimension of the whole dense family retained by the Philippon normal generic-curve alteration model https://prove2.me/theorems/fdd30f1a-b4bd-4bf7-9647-e2b0056ba8b8 . No global boundary regularization is assumed.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.Smooth.smoothOfRelativeDimension_of_fiber_dimension_of_preconnectedSpace
    {X Y : Scheme.{u}} [PreconnectedSpace X] (f : X ⟶ Y) [Smooth f]
    (y : Y) [Nonempty (f.fiber y)] (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) = (d : WithBot ℕ∞)) :
    SmoothOfRelativeDimension d f := by sorry
