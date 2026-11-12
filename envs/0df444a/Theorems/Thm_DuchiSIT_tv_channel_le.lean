-- Prove2me | Theorems.Thm_DuchiSIT_tv_channel_le
-- name    : DuchiSIT.tv_channel_le
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-11T18:21:50.192847+00:00
-- url     : https://prove2.me/theorems/9be14f8b-fc6e-41e4-b749-9a11781ae3e3
-- title:
--   Proposition 9.1.1 — contraction inequality
-- statement:
--   For every Markov kernel and every pair of input probability laws, their output total-variation distance is at most the Dobrushin row coefficient times their input total-variation distance. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_DuchiSIT_DobrushinCoefficient
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace DuchiSIT

theorem tv_channel_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K]
    (μ ν : ProbabilityMeasure X) :
    MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) ≤
      dobrushin K * MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X) := by sorry

end DuchiSIT
