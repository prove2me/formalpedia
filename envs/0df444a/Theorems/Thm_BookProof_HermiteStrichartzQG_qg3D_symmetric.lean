-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_qg3D_symmetric
-- name    : BookProof.HermiteStrichartzQG.qg3D_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:48:35.793199+00:00
-- url     : https://prove2.me/theorems/bbdfdecd-5d38-41a3-9038-ad792581a9ab
-- title:
--   `BookProof.HermiteStrichartzQG.qg3D_symmetric` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) : SymmetricOn hermiteCore (qg3DHermiteHamiltonian xi xiY V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.qg3D_symmetric` (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) : SymmetricOn hermiteCore (qg3DHermiteHamiltonian xi xiY V)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.qg3D_symmetric`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.qg3D_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.qg3D_symmetric (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) :
    SymmetricOn hermiteCore (qg3DHermiteHamiltonian xi xiY V) := by sorry
