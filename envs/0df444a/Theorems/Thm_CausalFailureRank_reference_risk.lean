-- Prove2me | Theorems.Thm_CausalFailureRank_reference_risk
-- name    : CausalFailureRank.reference_risk
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:52.287254+00:00
-- url     : https://prove2.me/theorems/f253f56d-a16e-416c-9a36-257d6958f2d1
-- title:
--   App. B.4 — reference controller risk
-- statement:
--   For every selection of a maximal bad-child tool, every stage $i\le N$, every unused set $R$ and $0<r\le1/4$, the untruncated reference controller started at $(i,R,r)$ has failure probability at most $r$. Its risk budget splits between the correct and error branches.
--
--   Differences from the source:
--   - reading: "any tool maximizing the bad-child rank" → all selections attaining the maximum; reason: the source allows any such tool
--   - encoding: stages $1,\dots,N+1$ (entry states $1,\dots,N+1$) → 0-based stages, terminal $i\ge N$, entry stage $i\le N$ as a hypothesis; reason: Lean indexing; a stage index beyond the terminal one does not exist in the source, so no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, p.18

import Mathlib
import Definitions.Def_CausalFailureRank_tapeLaw
import Definitions.Def_CausalFailureRank_refController

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Reference controller risk.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, p.18: "At every entry history the local error
probability e is at most p. In the third case the correct branch contributes risk at most r/2 and the
error branch at most pr′ ≤ r/2. The second case has the same bound, and the first has zero failure
risk. Induction therefore bounds reference risk by r."

**Formalization Note.** For every selection attaining the bad-child maximum, stage `i ≤ N`, `R` and real
`0 < r ≤ 1/4` (rationality plays no role). The untruncated world has no caps. -/
theorem reference_risk (I : Instance N q) (sel : Fin N → Finset (Fin q) → Option (Fin q))
    (hsel : IsBadChildSelection I sel) (i : ℕ) (hi : i ≤ N) (R : Finset (Fin q)) (r : ℝ) (hr : 0 < r)
    (hr' : r ≤ 1 / 4) :
    tapeLaw I {ω | ¬ SuccessFrom I .currentPay (noCaps N) (refAction I sel none i R r)
      (entryState I i R) ω} ≤ ENNReal.ofReal r := by sorry

end CausalFailureRank
