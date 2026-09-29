-- Prove2me | Theorems.Thm_BlockCycleRotation_tendsto_psiBuf
-- name    : BlockCycleRotation.tendsto_psiBuf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:58.406683+00:00
-- url     : https://prove2.me/theorems/29c0f2e0-eb4e-4494-8356-8fece22a3026
-- title:
--   $\psi_\beta \to \psi$ as $\beta \to 0^{+}$
-- statement:
--   For $0 \le x \le \tfrac12$,
--   $$\lim_{\beta \to 0^{+}} \psi_\beta(x) = \psi(x),$$
--   with the quantitative form $\psi(x) - \psi_\beta(x) \le 8\beta$.
--
--   The buffered cost function degenerates to the unbuffered one as the buffer vanishes, uniformly at a linear rate. This is what licenses reading the buffered analysis as a refinement of the unbuffered one rather than a separate model.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §3. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L371-L384

import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.tendsto_psiBuf {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Filter.Tendsto (fun β => psiBuf β x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (psi x)) := by sorry
