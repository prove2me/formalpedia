-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_reserve_boundary_partition
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_reserve_boundary_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:44:24.341665+00:00
-- url     : https://prove2.me/theorems/7b80a2aa-4761-4338-ac48-1bc3f51fa361
-- title:
--   Actual cap-constrained reserve partitions into ruin, zero contact, open HJB region and cap contact
-- statement:
--   At every strictly positive physical time of the unchanged original cap-constrained admissible Lévy dividend strategy, the actual prepayment reserve is either below zero, exactly zero, strictly inside the open HJB interval, or at the cap in the ENNReal.ofReal representation. This source invariant uses the actual IsAdmissibleLe cap condition and makes both boundary contacts explicit. It deliberately does not assume the zero/cap occupation sets have zero Lebesgue measure, or infer a sign for boundary generator terms.
-- source:
--   Original IsAdmissibleLe and riskProcess, Avram Proposition 4(i) open interval versus cap boundary.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_reserve_boundary_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    riskProcess X x D t ω < 0 ∨
    riskProcess X x D t ω = 0 ∨
    (0 < riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) < C) ∨
    (0 < riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) = C) := by sorry
