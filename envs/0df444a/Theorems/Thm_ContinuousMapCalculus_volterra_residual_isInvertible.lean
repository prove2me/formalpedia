-- Prove2me | Theorems.Thm_ContinuousMapCalculus_volterra_residual_isInvertible
-- name    : ContinuousMapCalculus.volterra_residual_isInvertible
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:08:23.242978+00:00
-- url     : https://prove2.me/theorems/6189cc3c-70f3-44f3-91e8-3c054728efc0
-- title:
--   Invertibility of the identity minus a continuous Volterra operator
-- statement:
--   Let V be a real Banach space, A:[0,1]→L(V,V) a continuous operator-valued function, and L a bounded linear operator on C([0,1],V) satisfying
--
--   $$ (L\gamma)(s)=\int_0^s A(r)\gamma(r)\,dr. $$
--
--   Then I−L is a continuous linear isomorphism. There is no smallness hypothesis on A. This is the linear invertibility needed for applying the implicit-function theorem to a nonlinear integral equation.
-- source:
--   Original Banach-space Volterra lemma for the linearization of the Picard integral equation. Teschl, Ordinary Differential Equations and Dynamical Systems, https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf, §2.3 equations (2.27)–(2.29) and §2.4 equation (2.49). The proof here uses exponential-weight conjugation and the Neumann-series inverse (Mathlib Units.oneSub), rather than the iterated-kernel proof in the source.

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Ring.Units
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem ContinuousMapCalculus.volterra_residual_isInvertible {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : C(Icc (0 : ℝ) 1,V →L[ℝ] V))
    (L : C(Icc (0 : ℝ) 1,V) →L[ℝ] C(Icc (0 : ℝ) 1,V))
    (hL : ∀ γ s, L γ s = ∫ r in 0..(s:ℝ),
      A (projIcc 0 1 zero_le_one r) (γ (projIcc 0 1 zero_le_one r))) :
    (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) 1,V) - L).IsInvertible := by sorry
