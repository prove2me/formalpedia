-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbesselBase
-- name    : BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:19:25.8822+00:00
-- url     : https://prove2.me/theorems/123ac097-c522-4445-8474-eb247d6a3af4
-- title:
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase` {x : ℝ} (hx : x ≠ 0) : HasDerivAt sbesselBase (Real.cos x / x - Real.sin x / x ^ 2) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase` {x : ℝ} (hx : x ≠ 0) : HasDerivAt sbesselBase (Real.cos x / x - Real.sin x / x ^ 2) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sbesselBase (Real.cos x / x - Real.sin x / x ^ 2) x := by sorry
