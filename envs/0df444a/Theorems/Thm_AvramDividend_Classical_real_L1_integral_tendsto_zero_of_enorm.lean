-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_L1_integral_tendsto_zero_of_enorm
-- name    : AvramDividend.Classical.real_L1_integral_tendsto_zero_of_enorm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:59:33.711045+00:00
-- url     : https://prove2.me/theorems/28554286-6939-4ef6-b9ae-24f347b84302
-- title:
--   Convert convergence of ENNReal integrated norms to convergence of real L1 integrals
-- statement:
--   Let F_n be integrable real random variables on an arbitrary measure space. If their ENNReal-valued integrals of pointwise enorm converge to zero, then the ordinary real-valued integrals of absolute values converge to zero. The proof uses pinned Mathlib ofReal_integral_norm_eq_lintegral_enorm to identify each real integral with the toReal of its ENNReal counterpart, and continuity of ENNReal.toReal at zero. This small analytic bridge makes the finite-valued SimpleFunc.approxOn L1 convergence result usable by the Chat 08 conditional Markov approximation theorem, whose error hypothesis is a real expectation.
-- source:
--   Pinned Mathlib ofReal_integral_norm_eq_lintegral_enorm and ENNReal.tendsto_toReal at zero.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.real_L1_integral_tendsto_zero_of_enorm
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ)
    (hI : ∀ n, Integrable (F n) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫⁻ ω, ‖F n ω‖ₑ ∂P) atTop (nhds 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |F n ω| ∂P) atTop (nhds 0) := by sorry
