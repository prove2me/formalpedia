-- Prove2me | Theorems.Thm_BookProof_LimitCircleExample_exists_smooth_potential_not_essentiallySelfAdjoint
-- name    : BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:05:51.520516+00:00
-- url     : https://prove2.me/theorems/d3c29d06-3e4c-46ba-87b7-e852fae82639
-- title:
--   `BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint` : ∃ (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V), ¬ EssentiallySelfAdjointOn (ccDomain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLimitCircleExample`.
--
--   `BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint` : ∃ (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V), ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV)
--
--   Formalization note: Lean 4 identifier `BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint`.

-- Generated from ChapterLimitCircleExample.lean — theorem BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.LimitCircleExample



open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint :
    ∃ (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V),
      ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by sorry
