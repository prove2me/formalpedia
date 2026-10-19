-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_wallHam_add_const
-- name    : BookProof.WallEsaBddBelow.wallHam_add_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T03:31:47.287927+00:00
-- url     : https://prove2.me/theorems/9edb0fe1-1e14-4328-bf5a-0948990a1959
-- title:
--   `BookProof.WallEsaBddBelow.wallHam_add_const` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (c : ℝ) : wallHam (fun x => V x + c) (hV.add contDiff_const) = wallHam V hV +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.wallHam_add_const` (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (c : ℝ) : wallHam (fun x => V x + c) (hV.add contDiff_const) = wallHam V hV + ((constOp c).toLinearMap ∘ₗ (ccDomain ℝ).subtype)
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.wallHam_add_const`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.wallHam_add_const
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterKatoRellichDeficiencyCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterWallEsaBddBelow
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

theorem BookProof.WallEsaBddBelow.wallHam_add_const (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (c : ℝ) :
    wallHam (fun x => V x + c) (hV.add contDiff_const)
      = wallHam V hV + ((constOp c).toLinearMap ∘ₗ (ccDomain ℝ).subtype) := by sorry
