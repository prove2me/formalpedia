-- Prove2me | Theorems.Thm_BlockCycleRotation_coprimeTriples_decompose
-- name    : BlockCycleRotation.coprimeTriples_decompose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:04.64237+00:00
-- url     : https://prove2.me/theorems/4a5503ba-cf37-4c5a-9eea-191e8d155d6b
-- title:
--   The triple sum, decomposed by pairs
-- statement:
--   **The triple sum, decomposed by pairs.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `Q_eq_tripleSum_decomposed`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L324-L354

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.coprimeTriples_decompose {m : ℕ} (hm : 0 < m) (f : ℕ → ℕ → ℕ → ℕ) :
    ∑ t ∈ coprimeTriples m, f t.1 t.2.1 t.2.2
      = ∑ p ∈ coprimePairs m, ∑ b' ∈ (Finset.Ico 1 (bBound m p.1 p.2)).filter
          (fun b' => p.1 ∣ (m - p.2 * b')), f p.1 p.2 b' := by sorry
