-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat
-- name    : AlgebraicGeometry.exists_specializes_of_closed_of_specialFibre_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/36f138fb-f732-5fb1-b5e0-e30bc5a74273
-- title:
--   Closed special points lie on positive-dimensional special components
-- statement:
--   Let $A_0$ be a discrete valuation ring (a commutative ring which is a domain and a discrete valuation ring), let $X_0$ be a scheme and let $\mathrm{toBase}_0 \colon X_0 \to \operatorname{Spec} A_0$ be a morphism of schemes, with $X_0$ integral and $\mathrm{toBase}_0$ proper, flat and locally of finite presentation. Assume, first, that some point $\eta$ of $X_0$ lies over the closed point of $\operatorname{Spec} A_0$ and is not closed in the sense that there is a point $y \neq \eta$ of $X_0$ with $\eta \rightsquigarrow y$ (that is, $y$ lies in the closure of $\{\eta\}$); and, second, let $x_0$ be a point of $X_0$ lying over the closed point of $\operatorname{Spec} A_0$ whose only specialisation is itself, i.e. every $y$ with $x_0 \rightsquigarrow y$ equals $x_0$. The conclusion is that there exists a point $\eta$ of $X_0$ over the closed point of $\operatorname{Spec} A_0$ which again admits a specialisation $y \neq \eta$, and which specialises to $x_0$, that is $\eta \rightsquigarrow x_0$.
--
--   This is the statement that the special fibre of a flat proper integral model over a discrete valuation ring has no isolated closed points once it has a non-closed point at all: every closed point of the special fibre lies in the closure of a non-closed special point, hence on a positive-dimensional component. It is used in the assembly of a semistable model of the full-level modular curve over a tame base, where it guarantees that each closed point of the special fibre lies on one of the components covered by the available charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_specializes_of_closed_of_specialFibre_of_flat
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]

    (hpos : ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ ∃ y : X₀, η ⤳ y ∧ y ≠ η)
    (x₀ : X₀) (hx₀ : toBase₀.base x₀ = closedPoint A₀) (hcl : ∀ y : X₀, x₀ ⤳ y → y = x₀) :
    ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧ η ⤳ x₀ := by sorry
