-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_case_2_split
-- name    : BundledExpansion.SeqSim.case_2_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:03.463076+00:00
-- url     : https://prove2.me/theorems/b484c4b8-4171-4f9d-a6da-6e13af793e73
-- title:
--   Proposition 1, Case 2 — split a joint expansion
-- statement:
--   Consider one feasible joint expansion over $[s,e]$, buying $Q_1$ and $Q_2$ at $s$. There is a split time $y\in(s,e)$ at which a sequential cycle buys $Q_1$ at $s$ and $Q_2$ at $y$. The quantities and purchase cost agree, and at $\beta=2$ so do the fixed costs. The holding costs satisfy
--
--   $$
--   H_{\mathrm{seq}}=H_{\mathrm{sim}}-(y-s)(h_1a_{12}+h_2a_{22})Q_2.
--   $$
--
--   This is the local comparison used for the $\beta=2$ endpoint. **Formalization Note** The paper’s printed difference has an extra $h_1$ outside the sum; the formula above uses $\sum_i h_i(y-s)a_{i2}Q_2$, matching the two holding-cost integrals. The strict demand-ratio guard makes the constructed cycle feasible. Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, Appendix pp. 3–4 (PDF 38–39), proof of Proposition 1, Case 2, equations (20)–(21)

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem case_2_split (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard)
    (S : SimCycle) (hV : S.Valid P) (hK : S.K = 1) :
    ∃ C : SeqCycle, C.Valid P ∧ C.start = S.start ∧ C.stop = S.stop ∧
      C.lead = 0 ∧ C.m = 1 ∧ C.τ 1 ∈ Set.Ioo S.start S.stop ∧
      C.leadQ P 0 = S.q P 0 0 ∧ C.followQ P = S.q P 0 1 ∧
      purchase P (C.plan P) = purchase P (S.plan P) ∧
      C.fixed P = S.fixed P 2 ∧
      holding P (C.plan P) C.start C.stop =
        holding P (S.plan P) S.start S.stop -
          (C.τ 1 - S.start) * w P 1 * S.q P 0 1 := by sorry

end BundledExpansion.SeqSim
