-- Prove2me | Theorems.Thm_DuchiSIT_dobrushin_le_tvContraction
-- name    : DuchiSIT.dobrushin_le_tvContraction
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-11T18:22:14.767297+00:00
-- url     : https://prove2.me/theorems/961a9fde-ab09-4f28-a054-b16b9afdc199
-- title:
--   Proposition 9.1.1 — sharpness of the row coefficient
-- statement:
--   For every Markov kernel, the Dobrushin row coefficient is at most the supremum of its output-to-input total-variation ratios over distinct input probability laws. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_DuchiSIT_TVContractionCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace DuchiSIT

theorem dobrushin_le_tvContraction {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    dobrushin K ≤ tvContraction K := by sorry

end DuchiSIT
