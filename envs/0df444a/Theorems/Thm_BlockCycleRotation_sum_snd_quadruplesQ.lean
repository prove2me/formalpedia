-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesQ
-- name    : BlockCycleRotation.sum_snd_quadruplesQ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:42.657983+00:00
-- url     : https://prove2.me/theorems/65e9480f-67a2-47ec-a97d-ab2d832c08e3
-- title:
--   `Q(n) = ∑_{d ∣ n} R(n/d)`
-- statement:
--   **`Q(n) = ∑_{d ∣ n} R(n/d)`.** Classifying quadruples by `d = gcd(a,a')`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `Q_eq_tripleSum`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L1163-L1224

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_snd_quadruplesQ {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ quadruplesAll (n / d), p.2.1 := by sorry
