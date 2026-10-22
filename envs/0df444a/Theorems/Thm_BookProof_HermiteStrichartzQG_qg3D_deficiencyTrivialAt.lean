-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_qg3D_deficiencyTrivialAt
-- name    : BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:01:28.634036+00:00
-- url     : https://prove2.me/theorems/9ae00cf9-12a2-4773-8701-e8437dfb4c62
-- title:
--   `BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt hermiteCore (qg3DHermiteHamiltonian xi x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt hermiteCore (qg3DHermiteHamiltonian xi xiY V) z
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.qg3D_deficiencyTrivialAt (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    DeficiencyTrivialAt hermiteCore (qg3DHermiteHamiltonian xi xiY V) z := by sorry
