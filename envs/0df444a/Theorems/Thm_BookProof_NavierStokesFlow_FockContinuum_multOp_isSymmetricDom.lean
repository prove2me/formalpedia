-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:09.474989+00:00
-- url     : https://prove2.me/theorems/30346fa0-83d7-45fb-b5e6-fd15b6b038c3
-- title:
--   `BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom` (μ : Measure X) {g : X → ℝ} (hg : Measurable g) : IsSymmetricDom (multOp μ hg)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockContinuum`.
--
--   `BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom` (μ : Measure X) {g : X → ℝ} (hg : Measurable g) : IsSymmetricDom (multOp μ hg)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom`.

-- Generated from ChapterNavierStokesFockContinuum.lean — theorem BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum


open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.NavierStokesFlow.FockContinuum.multOp_isSymmetricDom (μ : Measure X) {g : X → ℝ} (hg : Measurable g) :
    IsSymmetricDom (multOp μ hg) := by sorry
