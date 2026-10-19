-- Prove2me | Theorems.Thm_BookProof_WallEsaBddBelow_scalaronPlus_esa
-- name    : BookProof.WallEsaBddBelow.scalaronPlus_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:56:59.733662+00:00
-- url     : https://prove2.me/theorems/0d9d3739-5bbf-430b-8eaf-857939a1ce51
-- title:
--   `BookProof.WallEsaBddBelow.scalaronPlus_esa` {M alpha : ℝ} (halpha : 0 < alpha) (W : ℝ → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {c : ℝ} (hWc : ∀ x, -c ≤ W x) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWallEsaBddBelow`.
--
--   `BookProof.WallEsaBddBelow.scalaronPlus_esa` {M alpha : ℝ} (halpha : 0 < alpha) (W : ℝ → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {c : ℝ} (hWc : ∀ x, -c ≤ W x) : EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam (fun phi => BookProof.Starobinsky.starobinskyV M alpha phi + W phi) ((BookProof.ScalaronEsa.contDiff_starobinskyV M alpha).add hW))
--
--   Formalization note: Lean 4 identifier `BookProof.WallEsaBddBelow.scalaronPlus_esa`.

-- Generated from ChapterWallEsaBddBelow.lean — theorem BookProof.WallEsaBddBelow.scalaronPlus_esa
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
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.Starobinsky
open BookProof.WallEsaBddBelow



open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.WallEsaBddBelow.scalaronPlus_esa {M alpha : ℝ} (halpha : 0 < alpha) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {c : ℝ} (hWc : ∀ x, -c ≤ W x) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun phi => BookProof.Starobinsky.starobinskyV M alpha phi + W phi)
        ((BookProof.ScalaronEsa.contDiff_starobinskyV M alpha).add hW)) := by sorry
