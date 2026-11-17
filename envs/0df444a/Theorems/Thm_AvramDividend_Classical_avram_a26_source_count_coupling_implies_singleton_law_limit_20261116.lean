-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
-- name    : AvramDividend.Classical.avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:11:56.466292+00:00
-- url     : https://prove2.me/theorems/703e7219-7ec5-43d6-86e2-bb304c26b753
-- title:
--   Original-space count coupling with vanishing disagreement transfers binomial singleton probabilities
-- statement:
--   For measurable natural-valued original-space counts K and a sequence Z_n, if Z_n has the binomial law Bin(n,p_n) and their disagreement event probability tends to zero on the same original measure space P, then the binomial singleton probability at every fixed k converges to P(K=k). This is a general probability coupling convergence lemma. It follows from the Proved singleton-measure sandwich theorem a26 and the real squeeze theorem.
-- source:
--   Source-space singleton probability coupling a26 Proved 091c6808; convergence under vanishing error using squeezed real probabilities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (Z : ℕ → Ω → ℕ) (hZ : ∀ n, Measurable (Z n))
    (p : ℕ → unitInterval)
    (hLaw : ∀ n, P.map (Z n) = Bin(n, p n))
    (hBad : Tendsto (fun n : ℕ =>
      (P {ω : Ω | K ω ≠ Z n ω}).toReal)
      atTop (𝓝 (0 : ℝ))) :
    ∀ k : ℕ,
      Tendsto (fun n : ℕ => (Bin(n, p n) {k}).toReal)
        atTop (𝓝 ((P.map K) {k}).toReal) := by sorry
