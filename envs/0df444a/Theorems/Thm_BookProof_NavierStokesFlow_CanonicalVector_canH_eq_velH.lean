-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canH_eq_velH
-- name    : BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:21:48.828991+00:00
-- url     : https://prove2.me/theorems/dcd2c08f-10a9-4a8d-a382-fe32ba73ee68
-- title:
--   The Lean 4 theorem `canH_eq_velH` in the `ChapterNavierStokesCanonicalVector` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesCanonicalVector.lean — theorem BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH
import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH :
    (lpFiniteModes Vel).subtype.comp (canH A c)
      = (velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c)))) := by sorry
