-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_scoreSoftmax_layerNorm_ge
-- name    : BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:26:22.828009+00:00
-- url     : https://prove2.me/theorems/a0163835-41de-4efa-92e1-d95c82bd918b
-- title:
--   `BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge` {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (hd : 0 < d) {q : Fin d → ℝ} {k : Fin m → (Fin d → ℝ)} (hq : 0 < variance q) (hk : ∀ j, 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge` {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (hd : 0 < d) {q : Fin d → ℝ} {k : Fin m → (Fin d → ℝ)} (hq : 0 < variance q) (hk : ∀ j, 0 < variance (k j)) (j : Fin m) : Real.exp (-(beta * (2 * d))) / (m : ℝ) ≤ scoreSoftmax beta (fun l => ∑ i, layerNorm q i * layerNorm (k l) i) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterTotalVariance
open BookProof.ChapterSoftmaxSharpness
open ChapterTotalVariance
open BookProof.ChapterLayerNorm


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d : ℕ}

theorem BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (hd : 0 < d)
    {q : Fin d → ℝ} {k : Fin m → (Fin d → ℝ)} (hq : 0 < variance q)
    (hk : ∀ j, 0 < variance (k j)) (j : Fin m) :
    Real.exp (-(beta * (2 * d))) / (m : ℝ)
      ≤ scoreSoftmax beta (fun l => ∑ i, layerNorm q i * layerNorm (k l) i) j := by sorry
