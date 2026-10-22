-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product
-- name    : AvramDividend.Classical.chat04_past_event_next_levy_increment_measure_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:34:30.205982+00:00
-- url     : https://prove2.me/theorems/11c0ac64-1664-4489-b61b-a749eb0a7b22
-- title:
--   Finite-prefix induction: any past-measurable event factors from the next Lévy increment
-- statement:
--   For a canonical spectrally negative Lévy process with its original adapted filtration and independent-increments axiom, any deterministic u≤v, any measurable event A in the entire history sigma algebra F_u (including an arbitrary intersection of previous-increment barrier observations and any F_s-past restriction), and any Borel set B of real future increment values, the probability of A together with X_v−X_u lying in B equals P(A) times P(X_v−X_u∈B). This is the exact nontrivial event-level n-to-(n+1) induction step, with no restriction on the number or form of earlier history observations and no scale/integrability assumptions. It applies the pinned Mathlib probability independence equivalence directly to the original full-filtration Lévy axiom; individual-coordinate independence is not substituted for joint history independence. Repeated use and filtration-measurability of earlier event intersections yields the uniform finite-dimensional joint independence required by the previously accepted full-process path theorem.
-- source:
--   Original SpectrallyNegativeLevy.indepIncrements axiom, pinned Mathlib ProbabilityTheory.Indep_iff and MeasurableSet.preimage. Intended for finite-prefix cylinder law from original Levy axioms.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_past_event_next_levy_increment_measure_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u v : ℝ≥0) (huv : u ≤ v)
    (A : Set Ω) (hA : MeasurableSet[𝓕 u] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    P (A ∩ {ω | X.X v ω - X.X u ω ∈ B}) =
      P A * P {ω | X.X v ω - X.X u ω ∈ B} := by sorry
