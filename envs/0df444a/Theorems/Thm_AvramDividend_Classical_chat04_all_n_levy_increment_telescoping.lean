-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_all_n_levy_increment_telescoping
-- name    : AvramDividend.Classical.chat04_all_n_levy_increment_telescoping
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T11:55:42.920768+00:00
-- url     : https://prove2.me/theorems/cfe8b73d-6030-450c-b51b-8dadac274476
-- title:
--   Uniform telescoping of all finite Lévy increment sequences into cumulative reserve positions
-- statement:
--   For the canonical spectrally negative Lévy process, every sample path, every arbitrary sequence of nonnegative observation times and every natural n, the sum of all n consecutive real increments X_(t_(i+1))−X_(t_i), i=0,...,n−1 equals the cumulative path displacement X_(t_n)−X_(t_0). This is a uniform induction, not a fixed two/three-observation instance, and does not even require time monotonicity. It supplies the exact deterministic triangular cumulative-sum transformation from vectors of successive independent increments to vectors of observed shifted path positions. In combination with the joint finite increment-cylinder product law and measurable transformation of random vectors, it supports finite-dimensional future path independence from the earlier filtration, needed for the full-process killed Markov theorem. No stochastic independence is assumed in this purely algebraic pathwise lemma.
-- source:
--   Original SpectrallyNegativeLevy process path values; pinned Mathlib Finset.sum_range_succ and real ring arithmetic.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_all_n_levy_increment_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, (X.X (t (i + 1)) ω - X.X (t i) ω)) =
      X.X (t n) ω - X.X (t 0) ω := by sorry
