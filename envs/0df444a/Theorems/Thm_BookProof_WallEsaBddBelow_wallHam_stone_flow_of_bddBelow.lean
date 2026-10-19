-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_stone_flow_of_bddBelow
-- name    : BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T03:31:41.420234+00:00
-- url     : https://prove2.me/theorems/c21adfe4-be30-4728-8568-2f8bc521c13c
-- title:
--   `BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) : ∃ (T :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) : ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ))) (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))), IsSelfAdjointExtension (wallHam V hV) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.StoneBridge
open BookProof.WallEsaBddBelow



open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.WallEsaBddBelow.wallHam_stone_flow_of_bddBelow (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ)))
      (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))),
      IsSelfAdjointExtension (wallHam V hV) T.op ∧ IsStoneFlow T U := by sorry
