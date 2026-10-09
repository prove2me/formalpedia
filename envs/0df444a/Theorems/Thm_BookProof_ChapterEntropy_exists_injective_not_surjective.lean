-- Prove2me | Theorems.Thm_BookProof_ChapterEntropy_exists_injective_not_surjective
-- name    : BookProof.ChapterEntropy.exists_injective_not_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:50:43.197979+00:00
-- url     : https://prove2.me/theorems/2f7aa661-e519-4d50-8b39-c35c3fef081b
-- title:
--   `BookProof.ChapterEntropy.exists_injective_not_surjective` : ∃ f : ℕ → ℕ, Function.Injective f ∧ ¬ Function.Surjective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEntropy`.
--
--   `BookProof.ChapterEntropy.exists_injective_not_surjective` : ∃ f : ℕ → ℕ, Function.Injective f ∧ ¬ Function.Surjective f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEntropy.exists_injective_not_surjective`.

-- Generated from ChapterEntropy.lean — theorem BookProof.ChapterEntropy.exists_injective_not_surjective
import Mathlib
import Definitions.Def_ChapterEntropy
open BookProof.ChapterEntropy



open Filter Asymptotics
open scoped Topology

theorem BookProof.ChapterEntropy.exists_injective_not_surjective :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ¬ Function.Surjective f := by sorry
