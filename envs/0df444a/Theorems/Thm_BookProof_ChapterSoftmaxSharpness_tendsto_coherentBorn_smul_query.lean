-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_coherentBorn_smul_query
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:30.542796+00:00
-- url     : https://prove2.me/theorems/83287b47-c046-4a95-b063-a00bbbca1fbe
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) : Tendsto (fun c : ℝ => bornWeight (c • q) k j) atTop (𝓝 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) :
    Tendsto (fun c : ℝ => bornWeight (c • q) k j) atTop (𝓝 1) := by sorry
