-- Prove2me | Theorems.Thm_BlockCycleRotation_dConst_enclosure
-- name    : BlockCycleRotation.dConst_enclosure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:31.476464+00:00
-- url     : https://prove2.me/theorems/3ad88c02-c916-46f5-81fe-7036e3294b1b
-- title:
--   $1.84 \le D \le 1.85$
-- statement:
--   $$1.84 \le D \le 1.85 .$$
--
--   A two-sided certified enclosure of the constant appearing in Theorem 14, so that the paper's $D \approx 1.85$ is not merely asserted but bounded on both sides. The lower bound needs a row estimate from below, $\sum_{a'<a} g(a,a') \ge 5(a-1)/(9a^3)$, to complement the upper bound used for $D \le 1.85$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Thm A / Thm 14. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L660-L662

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.dConst_enclosure : (1.84 : ℝ) ≤ dConst ∧ dConst ≤ 1.85 := by sorry
