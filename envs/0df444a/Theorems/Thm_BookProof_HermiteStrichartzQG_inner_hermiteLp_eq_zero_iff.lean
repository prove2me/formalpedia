-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_inner_hermiteLp_eq_zero_iff
-- name    : BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T09:01:10.190993+00:00
-- url     : https://prove2.me/theorems/95e5ca8e-729b-40f8-894c-e300457a70cb
-- title:
--   `BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff` {w : L2R} : (∀ n : ℕ, (inner ℂ (hermiteLp n) w : ℂ) = 0) ↔ w = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff` {w : L2R} : (∀ n : ℕ, (inner ℂ (hermiteLp n) w : ℂ) = 0) ↔ w = 0
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.FarisLavine
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff {w : L2R} :
    (∀ n : ℕ, (inner ℂ (hermiteLp n) w : ℂ) = 0) ↔ w = 0 := by sorry
