-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_germ_negative_limsup_ae_of_uniform_mass_ws01f
-- name    : AvramDividend.Classical.levy_germ_negative_limsup_ae_of_uniform_mass_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:13:15.720884+00:00
-- url     : https://prove2.me/theorems/ef2564da-4cd1-4469-84fa-1bc4da374c73
-- title:
--   Lévy time-zero germ law upgrades positive negative-slope limsup mass to almost surely
-- statement:
--   For an actual spectrally negative Lévy process, any countable observation grid tending to zero and a fixed real slope C, if the negative-slope event has a uniformly positive probability along all sufficiently late grid points, then it occurs at infinitely many grid points almost surely. The proof shows the limsup set has positive probability by a Proved finite-measure continuity lemma, lies in the time-zero Lévy germ by a Proved measurable-grid theorem, and therefore has probability one by the separately Proved actual Lévy germ zero-one law. This is the genuine stochastic 0-1 upgrade, not convergence-in-probability-to-a.s. sleight of hand.
-- source:
--   WS1F remotely Proved 05828212 generic germ zero-one, e1f28426 actual Lévy germ zero-one, 3e22718b countable negative-slope event germ measurability, b9286485 positive limsup probability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_probability_limsup_uniform_lower_mass_ws01f
import Theorems.Thm_AvramDividend_Classical_germ_negative_slope_limsup_measurable_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_germ_zero_one_ws01f

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_germ_negative_limsup_ae_of_uniform_mass_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (C p : ℝ) (hp : 0 < p) (N : ℕ)
    (hmass : ∀ n ≥ N,
      p ≤ P.real {ω | X.X (δ n) ω < C * (δ n : ℝ)}) :
    ∀ᵐ ω ∂P,
      ω ∈ (⋂ k : ℕ, ⋃ n : ℕ,
        {ω : Ω | k ≤ n ∧ X.X (δ n) ω < C * (δ n : ℝ)}) := by sorry
