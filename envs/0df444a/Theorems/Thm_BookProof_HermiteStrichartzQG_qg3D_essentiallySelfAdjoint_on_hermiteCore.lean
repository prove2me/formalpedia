-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_qg3D_essentiallySelfAdjoint_on_hermiteCore
-- name    : BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:03:22.085143+00:00
-- url     : https://prove2.me/theorems/a78b4123-351b-46ef-923e-8626068bfcfb
-- title:
--   `BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (qg3DHermiteHamiltonian xi xi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (qg3DHermiteHamiltonian xi xiY V)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.qg3D_essentiallySelfAdjoint_on_hermiteCore (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (qg3DHermiteHamiltonian xi xiY V) := by sorry
