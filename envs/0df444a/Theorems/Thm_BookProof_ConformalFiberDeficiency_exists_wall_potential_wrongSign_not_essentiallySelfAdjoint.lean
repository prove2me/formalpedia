-- Prove2me | Theorems.Thm_BookProof_ConformalFiberDeficiency_exists_wall_potential_wrongSign_not_essentiallySelfAdjoint
-- name    : BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:18:26.215984+00:00
-- url     : https://prove2.me/theorems/a87a527a-a383-43e2-aae4-d4645c526944
-- title:
--   `BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint` : ∃ (U V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V), (∀ y, 0 ≤ U...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConformalFiberDeficiency`.
--
--   `BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint` : ∃ (U V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V), (∀ y, 0 ≤ U y) ∧ Tendsto U atBot atTop ∧ Tendsto U atTop (𝓝 0) ∧ (∀ y, V y = -24 * (U y + 1 / 32)) ∧ ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV)
--
--   Formalization note: Lean 4 identifier `BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint`.

-- Generated from ChapterConformalFiberDeficiency.lean — theorem BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Definitions.Def_ChapterConformalFiberDeficiency
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa



open MeasureTheory Real Filter Topology
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint :
    ∃ (U V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V),
      (∀ y, 0 ≤ U y) ∧ Tendsto U atBot atTop ∧ Tendsto U atTop (𝓝 0) ∧
        (∀ y, V y = -24 * (U y + 1 / 32)) ∧
        ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by sorry
