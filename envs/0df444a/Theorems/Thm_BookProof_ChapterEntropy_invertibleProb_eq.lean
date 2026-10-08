-- Prove2me | Theorems.Thm_BookProof_ChapterEntropy_invertibleProb_eq
-- name    : BookProof.ChapterEntropy.invertibleProb_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:47:41.133976+00:00
-- url     : https://prove2.me/theorems/df1278a8-d1cd-42c2-a64b-c772341a3b7d
-- title:
--   `BookProof.ChapterEntropy.invertibleProb_eq` (n : ℕ) : invertibleProb n = (Nat.factorial n : ℝ) / (n ^ n : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropy`.
--
--   `BookProof.ChapterEntropy.invertibleProb_eq` (n : ℕ) : invertibleProb n = (Nat.factorial n : ℝ) / (n ^ n : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropy.invertibleProb_eq`.

-- Generated from ChapterEntropy.lean — theorem BookProof.ChapterEntropy.invertibleProb_eq
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy



open Filter Asymptotics
open scoped Topology

theorem BookProof.ChapterEntropy.invertibleProb_eq (n : ℕ) :
    invertibleProb n = (Nat.factorial n : ℝ) / (n ^ n : ℝ) := by sorry
