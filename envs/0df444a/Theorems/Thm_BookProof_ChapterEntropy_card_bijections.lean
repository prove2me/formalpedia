-- Prove2me | Theorems.Thm_BookProof_ChapterEntropy_card_bijections
-- name    : BookProof.ChapterEntropy.card_bijections
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:47:22.573858+00:00
-- url     : https://prove2.me/theorems/ca755e95-0760-4e64-af17-e6e1d05007ef
-- title:
--   `BookProof.ChapterEntropy.card_bijections` (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropy`.
--
--   `BookProof.ChapterEntropy.card_bijections` (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropy.card_bijections`.

-- Generated from ChapterEntropy.lean — theorem BookProof.ChapterEntropy.card_bijections
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy



open Filter Asymptotics
open scoped Topology

theorem BookProof.ChapterEntropy.card_bijections (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by sorry
