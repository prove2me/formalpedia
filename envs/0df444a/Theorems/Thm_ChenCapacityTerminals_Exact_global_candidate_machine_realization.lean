-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_global_candidate_machine_realization
-- name    : ChenCapacityTerminals.Exact.global_candidate_machine_realization
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:10:24.715708+00:00
-- url     : https://prove2.me/theorems/dff645aa-671e-4b85-92ce-d3aa9459cc92
-- title:
--   Word-RAM realization of the two-orientation candidate wrapper
-- statement:
--   Given a word program $P$ satisfying the rooted headline reduction, implement the two-orientation wrapper with all headline resource guarantees. In rooted mode it runs $P$ unchanged. In global mode it executes $P$ at root $0$ for $G$ and for the reversed arc list, compares their entering-cut capacities, complements the second shore if selected, and emits the cheaper indicator vector. Besides the exact `WordOutput`, it exposes the two optimal intermediate shores $X,Y$. The trace consists of the two rooted traces and the constants account for the two runs plus linear list and scan overhead.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, global-minimum-cut reduction on PDF p.10 (paper p.8): compute a rooted minimum cut in $G$ and in $G^R$ and take the better result; Subsection 2.1 for the reversal/complement step. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_CandidateReduction

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.global_candidate_machine_realization
    (P : WordProgram) (hP : RootedHeadlineReduction P) :
    ∃ Q : WordProgram, CandidateReduction Q := by sorry
