-- Prove2me | Theorems.Thm_BookProof_SmHiggsVacuum_higgs_goldstone
-- name    : BookProof.SmHiggsVacuum.higgs_goldstone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:33.023977+00:00
-- url     : https://prove2.me/theorems/e1378562-27bc-4bcc-8f1d-28a27d05fa4a
-- title:
--   `BookProof.SmHiggsVacuum.higgs_goldstone` {lam mu2 : ℝ} {u w : E} (hu : lam * ‖u‖ ^ 2 = mu2) (hperp : (inner ℝ u w : ℝ) = 0) (t : ℝ) : higgsV lam mu2 (u + t • w) = higgsV lam mu2 u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHiggsVacuum`.
--
--   `BookProof.SmHiggsVacuum.higgs_goldstone` {lam mu2 : ℝ} {u w : E} (hu : lam * ‖u‖ ^ 2 = mu2) (hperp : (inner ℝ u w : ℝ) = 0) (t : ℝ) : higgsV lam mu2 (u + t • w) = higgsV lam mu2 u + (lam / 4) * t ^ 4 * ‖w‖ ^ 4
--
--   Formalization note: Lean 4 identifier `BookProof.SmHiggsVacuum.higgs_goldstone`.

-- Generated from ChapterSmHiggsVacuum.lean — theorem BookProof.SmHiggsVacuum.higgs_goldstone
import Mathlib
import Definitions.Def_ChapterSmHiggsVacuum
open BookProof.SmHiggsVacuum



open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.SmHiggsVacuum.higgs_goldstone {lam mu2 : ℝ} {u w : E} (hu : lam * ‖u‖ ^ 2 = mu2)
    (hperp : (inner ℝ u w : ℝ) = 0) (t : ℝ) :
    higgsV lam mu2 (u + t • w) = higgsV lam mu2 u + (lam / 4) * t ^ 4 * ‖w‖ ^ 4 := by sorry
