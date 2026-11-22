-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_scale_head_bound
-- name    : AvramDividend.Classical.p2m81_scale_head_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:34:20.460037+00:00
-- url     : https://prove2.me/theorems/38445e3c-9fb4-4252-9d10-f9e434c2edd8
-- title:
--   Scale head integral bound by monotonicity and exp integral
-- statement:
--   On (0,a] with W monotone up to a and nonnegative at a, the Laplace head integral of exp(-(beta*x))*W x is at most W a / beta. Helper D1 for parent fc6b315a: monotonicity bounds W x by W a, and the exp integral over (0,a] is at most the full (0,oo) value 1/beta from the Tauberian exp package via setIntegral_mono_set.
-- source:
--   Decomposition child D1 of fc6b315a. Proof uses child AB (p2m81_tauberian_exp_package) for integrability/value; statement is pure analysis with no project dependencies.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_scale_head_bound (W : ℝ → ℝ) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hMono : ∀ x : ℝ, x ∈ Ioc (0:ℝ) a → W x ≤ W a) (hWaNN : 0 ≤ W a)
    (hint : IntegrableOn (fun x : ℝ => Real.exp (-(β * x)) * W x) (Ioc (0:ℝ) a)) :
    (∫ x in Ioc (0:ℝ) a, Real.exp (-(β * x)) * W x) ≤ W a / β := by sorry
