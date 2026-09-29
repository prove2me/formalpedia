-- Prove2me | Theorems.Thm_BlockCycleRotation_Qgt_sub_G1_le
-- name    : BlockCycleRotation.Qgt_sub_G1_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:34.919148+00:00
-- url     : https://prove2.me/theorems/cbc57e41-31fb-445b-b6dd-6e2a524b73ff
-- title:
--   $Q^{>} = G_1 + O(n^{3/2+\varepsilon})$
-- statement:
--   For $n>0$,
--   $$\left| \sum_{q \in \mathcal{Q}(n),\, a<a'} (a+a') \;-\; G_1(n) \right| \le 5\,\mathrm{Err}(n),$$
--   with $\mathrm{Err}(n)$ the aggregate error of the three estimation layers.
--
--   This is the decomposition $Q^{>} = G_1 + G_2 + G_3$ of the paper, with $G_2$ and $G_3$ absorbed into the error: the restricted quadruple sum equals its main term up to $O(n^{3/2+\varepsilon})$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16 and 18. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L628-L689

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.Qgt_sub_G1_le {n : ℕ} (hn : 0 < n) :
    |((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n|
      ≤ 5 * Err n := by sorry
