-- Prove2me | Theorems.Thm_AlgoPFR_claim_4_11_access_cost
-- name    : AlgoPFR.claim_4_11_access_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:40.996237+00:00
-- url     : https://prove2.me/theorems/f82e4509-62af-40d0-8ee3-90a0160818ec
-- title:
--   Claim 4.11 — $\mathbb E[C_{\mathrm{access}}]\le24(d+L_0+1)$
-- statement:
--   In the context of Claim 4.10, with $C_{\mathrm{access}}$ the logarithmic cost overhead of one iteration,
--   $$\mathbb E[C_{\mathrm{access}}]\le24(d+L_0+1),$$
--   the expectation being over the fiber label and both bucket labels.
--
--   The overheads multiply when access procedures are composed across iterations, so recording them as logarithms lets them add up along a trajectory.
--
--   Differences from the source:
--
--   - reading: E[C_access], with the variables of the expectation unnamed → E over the fiber label and both bucket labels; reason: the printed proof's Eq. (47) averages over Z, J_X and J_Y
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 4.11, p.32

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 4.11.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.32: in the context of Claim 4.10, `E[C_access] ≤ 24 (d + L₀ + 1)`, where
`C_access` is defined by Eqs. (43)–(44) and the expectation is over the fiber labels and both bucket
labels. -/
theorem claim_4_11_access_cost {n : ℕ} (L₀ : ℝ) (s : AccessState n) (hX : IsAccess s.X s.MX)
    (hY : IsAccess s.Y s.MY) (hΔX : slack s.X s.MX ≤ L₀) (hΔY : slack s.Y s.MY ≤ L₀)
    (f : Family) :
    expect (familyOutcomeLaw f s) (cAccess f s) ≤ ENNReal.ofReal (24 * (s.dist + L₀ + 1)) := by sorry

end AlgoPFR
