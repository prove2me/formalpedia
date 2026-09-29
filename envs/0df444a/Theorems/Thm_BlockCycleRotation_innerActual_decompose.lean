-- Prove2me | Theorems.Thm_BlockCycleRotation_innerActual_decompose
-- name    : BlockCycleRotation.innerActual_decompose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:48.660656+00:00
-- url     : https://prove2.me/theorems/0384be68-9a59-4d1b-993c-aeb88e61a424
-- title:
--   The paper's decomposition
-- statement:
--   **The paper's decomposition** `Q(n,d,a,a') = G₁ + G₂ + G₃`.
--
--   In Blomer–Bux this is **Lemmas 16, 18 and 19**, “Decomposition `G₁ + G₂ + G₃`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemmas 16, 18 and 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L211-L215

import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.innerActual_decompose (m d a a' : ℕ) :
    innerActual m d a a' = G1term m d a a' + G2term m d a a' + G3term m d a a' := by sorry
