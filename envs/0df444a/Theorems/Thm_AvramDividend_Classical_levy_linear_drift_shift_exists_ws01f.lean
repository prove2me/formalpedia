-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_exists_ws01f
-- name    : AvramDividend.Classical.levy_linear_drift_shift_exists_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:57:09.153226+00:00
-- url     : https://prove2.me/theorems/0dede491-eba4-4fc2-9395-676828f40ace
-- title:
--   Deterministic linear drift subtraction preserves the actual spectrally negative Lévy law and shifts its exponent
-- statement:
--   For every original spectrally negative Lévy process and arbitrary real slope C, construct an actual spectrally negative Lévy process on the same filtered probability space whose sample paths are X_t−Ct, Gaussian and Lévy-measure parameters are unchanged, triplet drift coefficient decreases by C, and Laplace exponent becomes ψ(θ)−Cθ. The proof must reverify adaptedness, stationary independent increments, càdlàg paths, no positive jumps and the source exponential moment identity. This is the independent, source-faithful stochastic interface needed to deduce all cofinal Rogozin slopes from an eventual descending Wiener–Hopf factor.
-- source:
--   Canonical definition UUID 933ced80-71c1-4c0f-a6a7-ab7757fc97e9 and elementary deterministic affine transformation of a Lévy process; Mathlib IdentDistrib.sub_const and independence of measurable transforms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_linear_drift_shift_exists_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      (∀ (t : ℝ≥0) (ω : Ω),
        Y.X t ω = X.X t ω - C * (t : ℝ)) ∧
      (∀ θ : ℝ, Y.ψ θ = X.ψ θ - C * θ) := by sorry
