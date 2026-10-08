-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_tendsto_shannonEntropy_bornWeight_smul_query
-- name    : BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:56:13.80528+00:00
-- url     : https://prove2.me/theorems/571c781d-53de-4262-8569-a1e139e4900c
-- title:
--   `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query` {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query` {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) : Tendsto (fun c : ℝ => shannonEntropy (fun l => bornWeight (c • q) k l)) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_bornWeight_smul_query {n : ℕ}
    (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hk : ∀ l, ‖k l‖ = r) (j : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) :
    Tendsto (fun c : ℝ => shannonEntropy (fun l => bornWeight (c • q) k l)) atTop (𝓝 0) := by sorry
