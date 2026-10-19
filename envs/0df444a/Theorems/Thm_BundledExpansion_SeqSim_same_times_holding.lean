-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_same_times_holding
-- name    : BundledExpansion.SeqSim.same_times_holding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:06.099235+00:00
-- url     : https://prove2.me/theorems/6e94451e-233a-44fc-8a0c-79e36e234700
-- title:
--   §3.2 — joint replenishment reduces holding at fixed times
-- statement:
--   Take any feasible sequential cycle and keep all its expansion times fixed. A feasible simultaneous cycle can replenish both cluster types at those same times, and its holding cost is strictly smaller:
--
--   $$
--   H_{\mathrm{sim}}<H_{\mathrm{seq}}.
--   $$
--
--   This is the paper’s fixed-times comparison used at $\beta=1$. **Formalization Note** Continuous demand and the strict demand-ratio guard ensure a strict comparison; Assumption 1 by itself gives only non-strict interval inequalities. Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 13 (PDF 14); Appendix p. 3 (PDF 38), §3.2 remark; proof of Proposition 1, Case 1

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem same_times_holding (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (hC : C.Valid P) :
    ∃ S : SimCycle, S.Valid P ∧ S.start = C.start ∧ S.stop = C.stop ∧
      S.K = C.m + 1 ∧
      (∀ k ≤ C.m + 1, S.τ k = C.τ k) ∧
      holding P (S.plan P) S.start S.stop <
        holding P (C.plan P) C.start C.stop := by sorry

end BundledExpansion.SeqSim
