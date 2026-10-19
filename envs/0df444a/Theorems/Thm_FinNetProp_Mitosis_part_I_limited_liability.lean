-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_part_I_limited_liability
-- name    : FinNetProp.Mitosis.part_I_limited_liability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:33.483169+00:00
-- url     : https://prove2.me/theorems/987886ca-f3e1-4241-b20c-0877011df652
-- title:
--   Proof of Theorem 4.2, Part (I), p. 2808 — every solution of (2.1) leaves all agents with nonnegative equity
-- statement:
--   Let $F = (N, z, L)$ be a financial network and let $P \in \mathcal M(N)$ solve the system (2.1) for $F$. Then every agent ends up with nonnegative equity:
--   $$e_i(N, z, P) = z_i + \sum_{j \in N} (P_{ji} - P_{ij}) \ge 0, \qquad i \in N.$$
--
--   This is the step of Part (I) of the proof of Theorem 4.2 showing that the proportional rule satisfies limited liability (Axiom 3.2).
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2808, proof of Theorem 4.2, Part (I), paragraph 'For limited liability, …'

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem part_I_limited_liability (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, 0 ≤ equity F P i := by sorry

end FinNetProp.Mitosis
