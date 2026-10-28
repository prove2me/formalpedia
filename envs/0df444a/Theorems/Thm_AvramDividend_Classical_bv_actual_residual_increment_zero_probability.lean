-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
-- name    : AvramDividend.Classical.bv_actual_residual_increment_zero_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:35:54.642238+00:00
-- url     : https://prove2.me/theorems/5e61917b-ff60-41dd-8434-28d25b3707bc
-- title:
--   Exact exponential zero-increment probability of the actual finite-activity drift residual
-- statement:
--   For any two deterministic times s≤t, the actual bounded-variation Lévy drift residual Y_t=d t−X_t has probability exp(−λ(t−s)) of unchanged value across [s,t], where λ is finite negative-jump intensity. This transfers the already-Proved fixed-time zero-atom law by the actual Lévy process's stationary-increments axiom and Mathlib IdentDistrib.measure_mem_eq applied to the singleton of the deterministic drift increment. It is the principal quantitative ingredient for a dyadic-grid count of positive residual increments and for proving there is no continuous residual drift between jumps.
-- source:
--   Avram Palmowski Pistorius (2007), finite-activity Lévy structure; Prove2Me actual residual zero atom and stationary increments.

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_increment_zero_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω |
      ((t : ℝ) * X.drift - X.X t ω) -
        ((s : ℝ) * X.drift - X.X s ω) = 0} =
      Real.exp (-(((t - s : ℝ≥0) : ℝ) *
        (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
