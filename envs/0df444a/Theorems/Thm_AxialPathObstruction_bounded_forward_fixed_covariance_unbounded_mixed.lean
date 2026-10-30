-- Prove2me | Theorems.Thm_AxialPathObstruction_bounded_forward_fixed_covariance_unbounded_mixed
-- name    : AxialPathObstruction.bounded_forward_fixed_covariance_unbounded_mixed
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:23:08.205524+00:00
-- url     : https://prove2.me/theorems/d6251b02-2aae-4518-ae04-89f41318459d
-- title:
--   Fixed quadratic covariance does not bound length-weighted angular charge
-- statement:
--   For every real number $C$, there is a finite complex vertex list $V$ starting at zero, contained in $|z|^2\le5/16$, whose consecutive edges have nonnegative real parts, first edge $1/2$, and total displacement $1/2$. Its quadratic edge covariance has diagonal entries $1/4$, off-diagonal entry zero, and determinant $1/16$. Every later edge is nonzero and orthogonal to the first edge. Nevertheless the sum of their length-weighted angular charges with that first edge exceeds $C$. This is a geometric obstruction to covariance-only payment rules; no realization as a polynomial derivative tower is claimed.
-- source:
--   Private repository Amal-David/derivative-chain-prize at fb2d3b3438371d1ef39da0092241fb0db2bd6859; research-results/unrestricted-4r-20261027/formal/AxialPathObstruction.lean; SHA-256 ce69d2b671675fed81e24468ac93b488412b8e3469750059ff184ecce68eefbc

import Definitions.Def_DerivativeChainAxialPath_20261028
open AxialPathObstruction
set_option autoImplicit false

theorem AxialPathObstruction.bounded_forward_fixed_covariance_unbounded_mixed (C : ℝ) :
    ∃ V : List ℂ,
      V.head?=some 0 ∧
      (differences V).head?=some (1/2 : ℂ) ∧
      (∀ z ∈ V, Complex.normSq z ≤ 5/16) ∧
      (∀ v ∈ differences V, 0 ≤ v.re) ∧
      (differences V).sum=(1/2 : ℂ) ∧
      sxx (differences V)=1/4 ∧ sxy (differences V)=0 ∧ syy (differences V)=1/4 ∧
      covarianceDet (differences V)=1/16 ∧
      (∀ v ∈ (differences V).tail, v≠0 ∧ dot (1/2 : ℂ) v=0) ∧
      C < firstAngularCharge (differences V) := by sorry
