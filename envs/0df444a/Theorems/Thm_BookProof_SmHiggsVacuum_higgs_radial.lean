-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_higgs_radial
-- name    : BookProof.SmHiggsVacuum.higgs_radial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:30.498893+00:00
-- url     : https://prove2.me/theorems/c011efa6-2d61-440d-b614-6e1022ca3b4f
-- title:
--   `BookProof.SmHiggsVacuum.higgs_radial` {lam mu2 : ℝ} {u : E} (hu : lam * ‖u‖ ^ 2 = mu2) (t : ℝ) : higgsV lam mu2 ((1 + t) • u) = higgsV lam mu2 u + mu2 * ‖u‖ ^ 2 * t ^ 2 * (1 + t +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.higgs_radial` {lam mu2 : ℝ} {u : E} (hu : lam * ‖u‖ ^ 2 = mu2) (t : ℝ) : higgsV lam mu2 ((1 + t) • u) = higgsV lam mu2 u + mu2 * ‖u‖ ^ 2 * t ^ 2 * (1 + t + t ^ 2 / 4)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.higgs_radial`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.higgs_radial
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.higgs_radial {lam mu2 : ℝ} {u : E} (hu : lam * ‖u‖ ^ 2 = mu2) (t : ℝ) :
    higgsV lam mu2 ((1 + t) • u)
      = higgsV lam mu2 u + mu2 * ‖u‖ ^ 2 * t ^ 2 * (1 + t + t ^ 2 / 4) := by sorry
