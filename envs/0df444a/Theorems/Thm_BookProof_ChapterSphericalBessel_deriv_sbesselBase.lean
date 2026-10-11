-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBessel_deriv_sbesselBase
-- name    : BookProof.ChapterSphericalBessel.deriv_sbesselBase
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:38.462975+00:00
-- url     : https://prove2.me/theorems/23c7f047-9288-4619-b08b-cd910e42d590
-- title:
--   `BookProof.ChapterSphericalBessel.deriv_sbesselBase` {r : ℝ} (hr : r ≠ 0) : deriv sbesselBase r = Real.cos r / r - Real.sin r / r ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBessel`.
--
--   `BookProof.ChapterSphericalBessel.deriv_sbesselBase` {r : ℝ} (hr : r ≠ 0) : deriv sbesselBase r = Real.cos r / r - Real.sin r / r ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBessel.deriv_sbesselBase`.

-- Generated from ChapterSphericalBessel.lean — theorem BookProof.ChapterSphericalBessel.deriv_sbesselBase
import Mathlib
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel



open scoped Topology

theorem BookProof.ChapterSphericalBessel.deriv_sbesselBase {r : ℝ} (hr : r ≠ 0) :
    deriv sbesselBase r = Real.cos r / r - Real.sin r / r ^ 2 := by sorry
