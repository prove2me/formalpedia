-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_theorem_4_part_1
-- name    : AgriChain.LandAlloc.theorem_4_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:03.941894+00:00
-- url     : https://prove2.me/theorems/5f0d0738-c3e5-4584-bcad-d680c0690e13
-- title:
--   Theorem 4 part 1, p. 15 — a larger capacity-adjusted margin makes Processor 1 win at every harvest
-- statement:
--   In the two-region agri-chain under its standing assumptions, suppose Processor 1's capacity-adjusted profit margin is at least Processor 2's:
--   $$\frac{p^e-c_1-p_o}{K_1}\ \ge\ \frac{p^e-c_2-p_o}{K_2}.$$
--   Then for all harvests $y_1,y_2\ge0$ the willingness to pay satisfy $\bar p_1(y_1,y_2)\ge\bar p_2(y_1,y_2)$; that is, Processor 1 wins the price competition at every yield realization, so $R_1(x_1,x_2)$ is the whole yield space and $R_2(x_1,x_2)=\emptyset$.
--
--   This is the dominance case ("CP3 Scenarios 1 and 2") in which the more efficient processor always wins; in particular it covers the symmetric chain.
--
--   **Formalization Note.** The regions $R_i$ of p. 15 are defined by the sign of $\bar p_1-\bar p_2$, so the statement is phrased directly as $\bar p_2\le\bar p_1$ at every pair of nonnegative harvests. Only part 1 of Theorem 4 is posed.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 15, Theorem 4 part 1

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem theorem_4_part_1 (C : Chain) (hC : C.Standing)
    (hmargin : (C.pe - C.c2 - C.po) / C.K2 ≤ (C.pe - C.c1 - C.po) / C.K1) :
    ∀ y1 y2 : ℝ, 0 ≤ y1 → 0 ≤ y2 → wtp2 C y1 y2 ≤ wtp1 C y1 y2 := by sorry

end AgriChain.LandAlloc
