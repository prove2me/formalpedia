-- Prove2me | Theorems.Thm_BlockCycleRotation_K_append
-- name    : BlockCycleRotation.K_append
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:31.692031+00:00
-- url     : https://prove2.me/theorems/08341fa5-11e2-4d6c-940d-17018570fbdf
-- title:
--   Euler's continuant identity
-- statement:
--   **Euler's continuant identity.** Splitting a list at any interior point, `K (l₁ ++ l₂) = K l₁ · K l₂ + K (l₁.dropLast) · K (l₂.tail)`. This is the identity that turns a split continued-fraction expansion into a solution of `n = a·b + a'·b'`.
--
--   The paper uses this step without giving it a number; the formalization records it as “Euler's continuant identity”. It is used in the proofs of `heilbronn_surjective`, `quadExpansion_spec`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L37-L67

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_append : ∀ (l₁ l₂ : List ℕ), l₁ ≠ [] → l₂ ≠ [] →
    K (l₁ ++ l₂) = K l₁ * K l₂ + K l₁.dropLast * K l₂.tail := by sorry
