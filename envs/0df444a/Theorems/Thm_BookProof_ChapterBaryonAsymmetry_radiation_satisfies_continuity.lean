-- Prove2me | Theorems.Thm_BookProof_ChapterBaryonAsymmetry_radiation_satisfies_continuity
-- name    : BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:43:33.29864+00:00
-- url     : https://prove2.me/theorems/c43c277d-1b50-4578-888e-52a4cd20f66e
-- title:
--   The radiation law satisfies the FRW continuity equation with `w = 1/3`: `a · ρ_r'(a) + 3·(1 + 1/3)·ρ_r(a) = 0` for `a > 0`
-- statement:
--   The radiation law satisfies the FRW continuity equation with `w = 1/3`:
--   `a · ρ_r'(a) + 3·(1 + 1/3)·ρ_r(a) = 0` for `a > 0`. This fixes the dilution
--   exponent `4`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity` (module `BookProof.BaryonAsymmetry`), line-linked source: `ChapterBaryonAsymmetry.lean` lines 83–97.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBaryonAsymmetry.lean#L83-L97

-- Generated from ChapterBaryonAsymmetry.lean — theorem BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry












open Filter Topology

theorem BookProof.ChapterBaryonAsymmetry.radiation_satisfies_continuity (ρr0 a : ℝ) (ha : 0 < a) :
    a * deriv (fun x => radDensity ρr0 x) a + 3 * (1 + 1/3) * radDensity ρr0 a = 0 := by sorry
