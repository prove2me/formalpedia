-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_schedule_and_packing_realization
-- name    : ChenCapacityTerminals.Exact.schedule_and_packing_realization
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:43:48.550599+00:00
-- url     : https://prove2.me/theorems/97e2bec9-4731-43aa-9272-b30030e0dd95
-- title:
--   Sections 4–4.1 — rooted dyadic schedule and normalized black-box packing
-- statement:
--   Assuming the terminal construction of Theorem 2.1, the pinning and conditioning construction of Corollary 4.1, the conditioned batching algorithm of Theorem 3.2, and integral max-flow/min-cut answers, construct the complete prescribed-root reduction of Theorem 1.1.
--
--   For each dyadic lower-bound guess $L$, begin with $d=\lceil\sqrt n\rceil$. Probe the selected terminals, contract the pinned set to the root, test conditioning, and batch the next terminal group with threshold $U=2L$. Replace $d$ by $\max\{1,\lfloor d/2\rfloor\}$ and finish with a batch containing every remaining nonroot. At a good guess $L\le\lambda<2L$, the first batch meeting an optimal shore recovers an optimum, even when earlier probes missed it. The cheapest candidate over all scales is therefore optimal.
--
--   The proof must also establish the accounting in Eq. (6),
--   $$\widetilde O\!\left(M\left(\frac n{d_0}+d_0\right)\right)
--    =\widetilde O(M\sqrt n),$$
--   and the Section 4.1 modification using masses $a(v)=\lceil1+n\deg^-(v)/M\rceil$ and normalized network size $s(H)=|V(H)|+(n/M)|E(H)|$. Processing recursive depths independently and packing each block when its normalized size reaches $n$ gives $\widetilde O(\sqrt n)$ actual calls, each with $O(n)$ vertices and $O(M)$ arcs, while preserving all cut values and the outside-work bound. Raw preprocessing, zero-valued optima, incorrect guesses, and arbitrary lawful oracle ties are included.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, paper pp. 8–10 (PDF pp. 9–11), §4 schedule, proof of Theorem 1.1 including Eq. (6), and §4.1 “Counting full-size oracle calls”; uses Theorem 2.1, Corollary 4.1, and Theorem 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.schedule_and_packing_realization
    (hterm :
      ∃ C : ℝ, ∃ P : List TrulySubcubicAPSP.Instr, 0 < C ∧ TerminalTime P ∧
        ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ),
          TerminalParameters G r d L b t →
          (∃ c, LegalConstruction G.network r d L b t c) ∧
          ∀ c, LegalConstruction G.network r d L b t c →
            TerminalShape C G.network r d L b t c)
    (hpin :
      ∃ C : ℝ, ∃ k : ℕ, ∃ P : List TrulySubcubicAPSP.Instr, 0 < C ∧ PinningTime P ∧
        ∀ (G : IntegerInput) (r d : ℕ) (L : ℚ),
          TerminalParameters G r d L (indegreeMass G.network r)
            (separatorThreshold G.network d) →
          (∃ c, LegalConstruction G.network r d L
            (indegreeMass G.network r) (separatorThreshold G.network d) c) ∧
          ∀ c, LegalConstruction G.network r d L
            (indegreeMass G.network r) (separatorThreshold G.network d) c →
            PinningShape C k G.network r d L c)
    (hbatch :
      (∃ O, LawfulExactOracle O) ∧
      ∃ (P : ExactProgram) (C : ℝ) (k B : ℕ),
        0 < C ∧ 0 < B ∧ BatchAlgorithm P C k B)
    (horacle : ∃ O, LawfulWordOracle O) :
    ∃ P : WordProgram, RootedHeadlineReduction P := by sorry
