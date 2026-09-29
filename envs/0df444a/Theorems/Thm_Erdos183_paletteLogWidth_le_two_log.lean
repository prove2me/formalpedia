-- Prove2me | Theorems.Thm_Erdos183_paletteLogWidth_le_two_log
-- name    : Erdos183.paletteLogWidth_le_two_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:17:49.846522+00:00
-- url     : https://prove2.me/theorems/40b134ec-5ddb-4317-aad9-1a27e573ac7f
-- title:
--   The palette log-width is at most twice the logarithm
-- statement:
--   For every $H \ge 3$,
--
--   $$\text{paletteLogWidth}(H) \;\le\; 2\log H.$$
--
--   Together with the matching lower bound $\log H \le \text{paletteLogWidth}(H)$, this pins the width parameter to within a constant factor of $\log H$ — the step that turns the construction's internal parameters into the explicit $k^{1/3}/\log k$ shape of the final bound.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2335-L2348

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.paletteLogWidth_le_two_log (H : ℕ) (hH : 3 ≤ H) :
    (paletteLogWidth H : ℝ) ≤ 2 * Real.log (H : ℝ) := by sorry
