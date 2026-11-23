-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_global_reversal_realization
-- name    : ChenCapacityTerminals.Exact.global_reversal_realization
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:44:26.771819+00:00
-- url     : https://prove2.me/theorems/b5b936cd-9b98-4f29-b421-6811509bd51e
-- title:
--   Global minimum cut by two rooted orientations
-- statement:
--   Given a bounded-word reduction that returns an exact minimum entering shore for every prescribed root, construct one program meeting the complete rooted-or-global headline specification.
--
--   For a global instance, choose one vertex $r$ (possible because $n\ge2$) and run the rooted reduction on $G$ and on the reversed network $G^{\mathrm{rev}}$. Every nonempty proper sink side $X$ either avoids $r$ in $G$, or its complement avoids $r$ in $G^{\mathrm{rev}}$. Reverse the second returned shore back, compare the two original entering capacities, and return the cheaper candidate. Both optima therefore appear among the candidates. In prescribed-root mode the supplied program is used directly.
--
--   The wrapper must preserve all uniform volume, outside-work, call-count, and per-call bounds up to constant factors, including raw-input preprocessing and arbitrary oracle ties.
-- source:
--   Thomas Y. Chen, STOC 2027 submission #665, proof of Theorem 1.1, final paragraph of paper p. 9 (PDF p. 10), global-cut reduction by $G$ and $G^{\mathrm{rev}}$; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=10

import Definitions.Def_ChenCapacityTerminals_Exact_RootedHeadline

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.global_reversal_realization
    (P : WordProgram) (hP : RootedHeadlineReduction P) :
    ∃ Q : WordProgram, HeadlineReduction Q := by sorry
