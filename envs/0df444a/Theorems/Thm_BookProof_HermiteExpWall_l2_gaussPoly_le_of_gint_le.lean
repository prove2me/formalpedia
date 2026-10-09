-- Prove2me | Theorems.Thm_BookProof_HermiteExpWall_l2_gaussPoly_le_of_gint_le
-- name    : BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:11:50.811261+00:00
-- url     : https://prove2.me/theorems/5c19b2d6-62c7-4df8-b505-6c41fb716bd5
-- title:
--   `BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le` {q : Polynomial ℝ} {K : ℝ} (hK : 0 ≤ K) (N : ℕ) (h : gint (q * q) ≤ K ^ 2 * gaussMoment (2 * N)) : l2 (gaussPoly q) ≤ K * l2 (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteExpWall`.
--
--   `BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le` {q : Polynomial ℝ} {K : ℝ} (hK : 0 ≤ K) (N : ℕ) (h : gint (q * q) ≤ K ^ 2 * gaussMoment (2 * N)) : l2 (gaussPoly q) ≤ K * l2 (psi N)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le`.

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le
import Definitions.Def_ChapterStarobinskyPotential
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

theorem BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le {q : Polynomial ℝ} {K : ℝ} (hK : 0 ≤ K) (N : ℕ)
    (h : gint (q * q) ≤ K ^ 2 * gaussMoment (2 * N)) :
    l2 (gaussPoly q) ≤ K * l2 (psi N) := by sorry
