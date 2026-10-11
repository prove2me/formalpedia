-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_oscillator_eigenfunction
-- name    : BookProof.HermiteStrichartzQG.oscillator_eigenfunction
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:48:25.426477+00:00
-- url     : https://prove2.me/theorems/316c09f9-037f-4508-a72c-4979ad2f73a0
-- title:
--   `BookProof.HermiteStrichartzQG.oscillator_eigenfunction` (n : ℕ) (x : ℝ) : -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x = oscillatorSymbol n * hermiteFun n x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.oscillator_eigenfunction` (n : ℕ) (x : ℝ) : -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x = oscillatorSymbol n * hermiteFun n x
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.oscillator_eigenfunction`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.oscillator_eigenfunction
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.oscillator_eigenfunction (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x
      = oscillatorSymbol n * hermiteFun n x := by sorry
