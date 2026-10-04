-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_intertwined_canH
-- name    : BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:45:34.513692+00:00
-- url     : https://prove2.me/theorems/f4d26333-9655-49e2-9922-3fdf74acf012
-- title:
--   The Lean 4 theorem `intertwined_canH` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `intertwined_canH` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH :
    Intertwined (canH A c) (nsDiffH A (fun j => Real.sqrt 2 * c j)) := by sorry
