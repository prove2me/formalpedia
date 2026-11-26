-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_seriesTsum_le
-- name    : ClassicalComplexWPT.norm_seriesTsum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:40.329894+00:00
-- url     : https://prove2.me/theorems/841182ab-7cc3-57fb-8fd4-e07fbfb5ba24
-- title:
--   Classical Complex WPT: norm series Tsum le
-- statement:
--   The Classical Complex WPT construction uses the norm series Tsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalSum.lean#L35-L38
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalSum.lean#L35-L38

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Definitions.Def_ClassicalComplexWPT_NormalSum
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
open ClassicalComplexWPT
variable {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
omit [CompleteSpace F]

theorem ClassicalComplexWPT.norm_seriesTsum_le (p : I → FormalMultilinearSeries 𝕜 E F)
    (hcoeff : ∀ n, Summable (fun i ↦ ‖p i n‖)) (n : ℕ) :
    ‖seriesTsum p n‖ ≤ ∑' i, ‖p i n‖ := by sorry
