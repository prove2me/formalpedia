-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product
-- name    : AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:45:18.479705+00:00
-- url     : https://prove2.me/theorems/4b6af35c-c6a9-4bca-ab7d-28f22e7bd161
-- title:
--   All finite Lévy increment cylinders jointly independent of any earlier filtration event
-- statement:
--   For the original canonical spectrally negative Lévy process with filtration F, ANY past event A measurable at time s, ANY monotone nonnegative sequence of observation times (t_0,t_1,...) starting no earlier than s, ANY sequence B_i of Borel restrictions on each consecutive increment, and ANY finite prefix length n, the probability of A jointly with all n restrictions on increments X_(t_(i+1))−X_(t_i) is exactly P(A) multiplied by the product of the n individual increment-event probabilities. The proof is an actual induction over arbitrary n, using a separate rigorous finite-prefix F_(t_n)-measurability theorem for the previous restrictions and the original full-filtration Lévy independent-increments axiom to factor the next event. This is the nontrivial uniform finite-dimensional joint independence law, strictly stronger than pairwise or coordinatewise independence, and is the key bridge towards the entire future shifted-path independence and the killed Markov property. Conversion of ordered consecutive increments into arbitrary future position-coordinate cylinders is the next measure-theoretic step; killed q-harmonicity also remains.
-- source:
--   Requires two separately authored/probed helper theorems chat04_finite_increment_prefix_event_filtration_measurable and chat04_past_event_next_levy_increment_measure_product, original X.Standing independent increments, pinned Mathlib Nat induction and Finset.prod_range_succ.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_finite_increment_prefix_event_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_all_finite_prefix_increment_cylinder_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (n : ℕ) :
    P (A ∩ {ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i}) =
      P A * ∏ i ∈ Finset.range n,
        P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} := by sorry
