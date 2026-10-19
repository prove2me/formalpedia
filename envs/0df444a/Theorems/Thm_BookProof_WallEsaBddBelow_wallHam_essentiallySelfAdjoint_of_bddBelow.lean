-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_essentiallySelfAdjoint_of_bddBelow
-- name    : BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T03:31:42.284264+00:00
-- url     : https://prove2.me/theorems/d492e7c3-3813-43ce-9ef7-4b62e6456ae8
-- title:
--   `BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) : EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV)
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.WallEsaBddBelow



open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.WallEsaBddBelow.wallHam_essentiallySelfAdjoint_of_bddBelow (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by sorry
