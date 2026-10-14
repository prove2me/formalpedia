-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_coherentBorn_smul_query_ne
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:32.172063+00:00
-- url     : https://prove2.me/theorems/0384c91f-c44a-49bc-9d19-c9c9de8a3dc6
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j i : Fi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j i : Fin m) (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) (hi : i ≠ j) : Tendsto (fun c : ℝ => bornWeight (c • q) k i) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j i : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) (hi : i ≠ j) :
    Tendsto (fun c : ℝ => bornWeight (c • q) k i) atTop (𝓝 0) := by sorry
