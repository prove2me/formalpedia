-- Prove2me | Theorems.Thm_BlockCycleRotation_psiBuf_rec
-- name    : BlockCycleRotation.psiBuf_rec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:19.829924+00:00
-- url     : https://prove2.me/theorems/96e88c2b-9f9c-4ee2-b457-6a2a3effa670
-- title:
--   Equation (def-mu-nu): the recursion for the buffered cost
-- statement:
--   For $0 < \beta < x \le \tfrac12$,
--   $$\psi_\beta(x) = 2x + \mathrm{Out}(x)\,\psi_{\beta/\mathrm{Out}(x)}\bigl(\mathrm{In}(x)\bigr).$$
--
--   The buffered analogue of the recursion defining $\psi$, the paper's equation (def-mu-nu). Off the terminating branch the buffer keeps its absolute size while the subproblem shrinks by the factor $\mathrm{Out}(x)$, so its *relative* size in the subproblem is $\beta/\mathrm{Out}(x)$ — which is why the buffer becomes progressively more effective as the recursion descends.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 13. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L122-L162

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.psiBuf_rec {β x : ℝ} (hβ : 0 < β) (hx : β < x) (hx2 : x ≤ 1 / 2) :
    psiBuf β x = 2 * x + Outt x * psiBuf (β / Outt x) (Inn x) := by sorry
