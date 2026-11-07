-- Prove2me | Theorems.Thm_BalancedKneser_proposition_B_5
-- name    : BalancedKneser.proposition_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:48.895195+00:00
-- url     : https://prove2.me/theorems/173fff93-72e3-4f54-adb3-203a545bc428
-- title:
--   Proposition B.5 (The nine-point vanishing) — $\tilde H_j(C_2(9,3);\mathbb Z)=0$ for $0\le j\le 7$
-- statement:
--   Let $C_2(9,3)$ be the simplicial complex on the $84$ three-element subsets of $[9]$ whose nonempty faces are the families of triples with a common Johnson center of radius two; for triples this means a $3$-set meeting every member of the family. Then its reduced integral homology vanishes through degree seven:
--   $$
--   \tilde H_j\big(C_2(9,3);\mathbb Z\big)=0\qquad(0\le j\le 7).
--   $$
--
--   This is one of the two finite inputs (11.1) of the radius-two comparison Theorem 11.1.
--
--   **Formalization Note** Homology is singular homology of the realization; $\tilde H_0=0$ is encoded as path-connectedness and $\tilde H_j=H_j$ for $j\ge1$.
--
--   Differences from the source:
--   - encoding: reduced simplicial homology H̃_j(C₂(9, 3); ℤ) = 0 for 0 ≤ j ≤ 7 → |C₂(9, 3)| path-connected and singular H_j(|C₂(9, 3)|; ℤ) trivial for 1 ≤ j ≤ 7; reason: for a nonempty complex H̃₀ = 0 means connected and H̃_j = H_j for j ≥ 1; simplicial and singular homology agree; C₂(9, 3) is nonempty
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Proposition B.5, p.38 (PDF p.40); C₂(9, 3), App. B, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_CC
import Definitions.Def_BalancedKneser_IsReducedAcyclicThrough

namespace BalancedKneser

/-- **Proposition B.5 (The nine-point vanishing)** (Alipour–Jafari, arXiv:2611.04486v1, p.38
(PDF p.40)): "H̃_j(C2(9, 3); Z) = 0 for 0 ≤ j ≤ 7."

`C₂(9, 3)` is the complex on the 84 triples of `[9]` whose faces are the nonempty families with
a common Johnson center of radius two, i.e. (App. B, p.35) a 3-set meeting every member.

Formalization Note: reduced integral homology of the complex is that of its realization;
`H̃₀ = 0` is encoded as path-connectedness (the complex is nonempty), and `H̃_j = H_j` for
`j ≥ 1` (`IsReducedAcyclicThrough`). -/
theorem proposition_B_5 : IsReducedAcyclicThrough ℤ (TreeCoverLB.realization (CC 2 9 3)) 7 := by sorry

end BalancedKneser
