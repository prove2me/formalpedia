-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_log_derivative_flatness
-- name    : AvramDividend.Classical.unbounded_esscher_log_derivative_flatness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:50:29.429384+00:00
-- url     : https://prove2.me/theorems/3d2b9177-643d-46c1-8fb5-24f7f454d996
-- title:
--   Vanishing logarithmic derivative of the Esscher-tilted scale function at infinity
-- statement:
--   Let W be the q-scale function of an unbounded-variation spectrally negative Levy process, q>0. Let phi>0 solve psi(phi)=q, and suppose its Esscher tilt V(x)=exp(-phi*x)W(x) is positive, differentiable and nondecreasing for x>0, with nonincreasing logarithmic derivative g=(log V)'. Then g tends to 0 as x tends to positive infinity. The proof uses the Laplace transform of W at parameters above phi: if the decreasing nonnegative derivative had a strictly positive limit, V would grow at least exponentially at some rate epsilon>0, contradicting the scale-function Laplace integrability at phi+epsilon. This supplies the mathematically necessary flat-tail condition for recovering an atomless excursion-height measure from g. The statement fixes the flawed previously authored integrable-at-infinity formulation, whose tail integral is independent of x.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, scale-function Esscher tilt asymptotics and Laplace transform; Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, excursion-height representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_esscher_log_derivative_flatness
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (htilt : MonotoneOn V (Ioi (0 : ℝ)))
    (hanti : AntitoneOn
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      (Ioi (0 : ℝ))) :
    Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      atTop (nhds (0 : ℝ)) := by sorry
