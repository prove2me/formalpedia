-- Prove2me | Theorems.Thm_BookProof_ChapterBaryonAsymmetry_matter_satisfies_continuity
-- name    : BookProof.ChapterBaryonAsymmetry.matter_satisfies_continuity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:42:51.063915+00:00
-- url     : https://prove2.me/theorems/ed34ecf0-b9b0-40ff-81ee-051adcf11a59
-- title:
--   The matter law satisfies the FRW continuity equation with `w = 0`: `a · ρ_m'(a) + 3·(1 + 0)·ρ_m(a) = 0` for `a > 0`
-- statement:
--   The matter law satisfies the FRW continuity equation with `w = 0`:
--   `a · ρ_m'(a) + 3·(1 + 0)·ρ_m(a) = 0` for `a > 0`. This fixes the dilution
--   exponent `3`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterBaryonAsymmetry.matter_satisfies_continuity` (module `BookProof.BaryonAsymmetry`), line-linked source: `ChapterBaryonAsymmetry.lean` lines 67–81.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBaryonAsymmetry.lean#L67-L81

-- Generated from ChapterBaryonAsymmetry.lean — theorem BookProof.ChapterBaryonAsymmetry.matter_satisfies_continuity
import Mathlib
import Definitions.Def_ChapterBaryonAsymmetry
open BookProof.ChapterBaryonAsymmetry












open Filter Topology

theorem BookProof.ChapterBaryonAsymmetry.matter_satisfies_continuity (ρm0 a : ℝ) (ha : 0 < a) :
    a * deriv (fun x => matterDensity ρm0 x) a + 3 * (1 + 0) * matterDensity ρm0 a = 0 := by sorry
