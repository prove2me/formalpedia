-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
-- name    : AvramDividend.Classical.bv_actual_residual_zero_atom_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:43:30.843471+00:00
-- url     : https://prove2.me/theorems/b9e50974-b743-407d-99b3-4f9c2842a0d8
-- title:
--   Actual finite-activity Lévy drift residual has exact zero-atom exponential survival
-- statement:
--   For the actual bounded-variation finite-activity spectrally negative Lévy process, the probability that its drift residual Y_t=dt-X_t is exactly zero equals exp(-λt), where λ is the negative-jump Lévy intensity. The general proved nonnegative Laplace zero-atom theorem, the proved actual-residual Laplace limit, adaptedness/measurability, and fixed-time drift upper bound give a fully rigorous identification, without postulating a compound-Poisson copy.
-- source:
--   Avram, Palmowski, Pistorius (2007) bounded variation and first-jump law; pinned Mathlib and existing accepted Prove2Me theorems.

import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_laplace_tendsto_survival
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Separation.Hausdorff

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_residual_zero_atom_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ) * X.drift - X.X t ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
