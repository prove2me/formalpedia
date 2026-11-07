-- Prove2me | Theorems.Thm_BalancedKneser_proposition_C_8
-- name    : BalancedKneser.proposition_C_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:12.525824+00:00
-- url     : https://prove2.me/theorems/bba46208-9644-484c-96f6-39b737ba61f2
-- title:
--   Proposition C.8 (The eight-point vanishing) — $\tilde H_j(C_2(8,4);\mathbb Z)=0$ for $0\le j\le 7$
-- statement:
--   Let $C_2(8,4)$ be the simplicial complex on the $70$ four-element subsets of $[8]$ whose nonempty faces are the families with a common $4$-set center $Z$ at Johnson distance at most two, i.e. $|A\cap Z|\ge2$ for every member $A$. Then
--   $$
--   \tilde H_j\big(C_2(8,4);\mathbb Z\big)=0\qquad(0\le j\le 7).
--   $$
--
--   This is the second finite input (11.1) of Theorem 11.1.
--
--   **Formalization Note** Homology is singular homology of the realization; $\tilde H_0=0$ is encoded as path-connectedness and $\tilde H_j=H_j$ for $j\ge1$.
--
--   Differences from the source:
--   - encoding: reduced simplicial homology H̃_j(C₂(8, 4); ℤ) = 0 for 0 ≤ j ≤ 7 → |C₂(8, 4)| path-connected and singular H_j(|C₂(8, 4)|; ℤ) trivial for 1 ≤ j ≤ 7; reason: for a nonempty complex H̃₀ = 0 means connected and H̃_j = H_j for j ≥ 1; simplicial and singular homology agree; C₂(8, 4) is nonempty
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Proposition C.8, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_BalancedKneser_CC
import Definitions.Def_BalancedKneser_IsReducedAcyclicThrough

namespace BalancedKneser

/-- **Proposition C.8 (The eight-point vanishing)** (Alipour–Jafari, arXiv:2611.04486v1, p.45
(PDF p.47)): "H̃_j(C2(8, 4); Z) = 0 for 0 ≤ j ≤ 7."

`C₂(8, 4)` is the complex on the 70 four-subsets of `[8]` whose faces are the nonempty families
with a common 4-set center `Z` at Johnson distance at most two (`|A ∩ Z| ≥ 2`).

Formalization Note: reduced integral homology of the realization, with `H̃₀ = 0` encoded as
path-connectedness (`IsReducedAcyclicThrough`). -/
theorem proposition_C_8 : IsReducedAcyclicThrough ℤ (TreeCoverLB.realization (CC 2 8 4)) 7 := by sorry

end BalancedKneser
