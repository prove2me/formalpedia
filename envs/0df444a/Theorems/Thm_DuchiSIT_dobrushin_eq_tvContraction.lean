-- Prove2me | Theorems.Thm_DuchiSIT_dobrushin_eq_tvContraction
-- name    : DuchiSIT.dobrushin_eq_tvContraction
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-11T18:22:29.396919+00:00
-- url     : https://prove2.me/theorems/9dfce98d-3407-4f2e-9bd5-0bae092e9a56
-- title:
--   Proposition 9.1.1 — exact total-variation contraction coefficient
-- statement:
--   For every Markov kernel between arbitrary measurable spaces, its Dobrushin row coefficient equals its strong total-variation data-processing coefficient. Both coefficients are independently defined using the same event-supremum total-variation normalization. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_DuchiSIT_TVContractionCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace DuchiSIT

theorem dobrushin_eq_tvContraction {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] :
    dobrushin K = tvContraction K := by sorry

end DuchiSIT
