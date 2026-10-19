-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_part_I_priority_of_creditors
-- name    : FinNetProp.Mitosis.part_I_priority_of_creditors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:43.645789+00:00
-- url     : https://prove2.me/theorems/263260ab-b80d-4248-b5b2-c6f68cd3a818
-- title:
--   Proof of Theorem 4.2, Part (I), p. 2808 — under a solution of (2.1), an agent who does not pay all its liabilities has zero equity
-- statement:
--   Let $F = (N, z, L)$ be a financial network and let $P \in \mathcal M(N)$ solve the system (2.1) for $F$. If agent $i \in N$ does not pay its liabilities in full, in the sense that its row satisfies $P_i < L_i$ (that is, $P_{ij} \le L_{ij}$ for all $j \in N$ and $P_{ik} < L_{ik}$ for some $k \in N$), then
--   $$e_i(N, z, P) = 0.$$
--
--   This is the step of Part (I) of the proof of Theorem 4.2 showing that the proportional rule satisfies priority of creditors (Axiom 3.3).
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2808, proof of Theorem 4.2, Part (I), paragraph 'Next, we show priority of creditors to hold. …'

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem part_I_priority_of_creditors (F : FinNet) (P : ℕ → ℕ → ℝ) (hP : IsPropSolution F P) :
    ∀ i ∈ F.N, RowLt F.N P F.L i → equity F P i = 0 := by sorry

end FinNetProp.Mitosis
