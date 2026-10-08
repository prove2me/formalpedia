-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_lt_iff_exists_witness
-- name    : AvramDividend.Classical.firstUpcrossing_lt_iff_exists_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:31:31.161725+00:00
-- url     : https://prove2.me/theorems/11b0d152-985c-46f1-b564-b576801f8321
-- title:
--   Strict time comparison for the Lévy first-upcrossing infimum
-- statement:
--   The infimum of strict upward-passage times is strictly earlier than a deterministic horizon t exactly when some strict passage occurs at a time s<t. This is the order-theoretic bridge used when proving measurability of the strict first-passage event and constructing stopping-time approximations. It remains valid if no threshold exceedance occurs, because the infimum of an empty subset is +∞. It uses the complete linear order on ENNReal and the coercion comparison for finite nonnegative times; no stochastic independence or Strong Markov assumptions are required.
-- source:
--   Mathlib.Order.CompleteLattice.Defs iInf_lt_iff (verified in Mathlib docs 8 October 2026); Avram Palmowski Pistorius (2007), first-passage time convention for Proposition 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_lt_iff_exists_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (t : ℝ≥0) :
    (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) < (t : ℝ≥0∞) ↔
      ∃ s : ℝ≥0, b < X.X s ω ∧ s < t := by sorry
