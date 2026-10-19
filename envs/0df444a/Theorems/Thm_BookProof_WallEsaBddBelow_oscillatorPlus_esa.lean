-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_oscillatorPlus_esa
-- name    : BookProof.WallEsaBddBelow.oscillatorPlus_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T03:31:45.680139+00:00
-- url     : https://prove2.me/theorems/dd307982-7ebd-4516-bfe4-75cb9bc9ccf3
-- title:
--   `BookProof.WallEsaBddBelow.oscillatorPlus_esa` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) : EssentiallySelfAdjointOn (ccDomain...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.oscillatorPlus_esa` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) : EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam (fun x => x ^ 2 / 4 + V x) (((contDiff_id.pow 2).div_const 4).add hV))
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.oscillatorPlus_esa`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.oscillatorPlus_esa
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

theorem BookProof.WallEsaBddBelow.oscillatorPlus_esa (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun x => x ^ 2 / 4 + V x)
        (((contDiff_id.pow 2).div_const 4).add hV)) := by sorry
