-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
-- name    : AvramDividend.Classical.levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:35:52.779993+00:00
-- url     : https://prove2.me/theorems/923863b7-543e-4ddf-8e26-f7249d48d98c
-- title:
--   Finite stopping-time cylinder reward strong-Markov factorisation without extra measurability
-- statement:
--   For every finite set of observation times and bounded continuous nonnegative reward of the corresponding future Lévy increments, the expectation restricted to an event in the stopped history is its probability times the unshifted expectation, with all measurability obtained from the process assumptions.
-- source:
--   Exact finite-dimensional consequence of the proved canonical no-meas scalar stopped-time Markov theorem, feeding compact-test uniqueness of finite cylinder measures and then full-path strong Markov result 61930a38-11f1-449e-bbb6-67d59c6d5ca8.

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_scalar_markov_no_meas_premise

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0)
    (h : (J → ℝ) → ℝ≥0∞)
    (hh : Continuous h) (hhm : Measurable h)
    (C : ℝ≥0∞) (hbound : ∀ z, h z ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => h (fun j : J =>
        X.X (τ ω' + (j : ℝ≥0)) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, h (fun j : J => y (j : ℝ≥0))
      ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  sorry
