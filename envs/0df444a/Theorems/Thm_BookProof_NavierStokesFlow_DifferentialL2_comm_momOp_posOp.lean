-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_comm_momOp_posOp
-- name    : BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:04:05.714823+00:00
-- url     : https://prove2.me/theorems/e1e53776-4452-49eb-9b35-5b05d3884d0a
-- title:
--   The Lean 4 theorem `comm_momOp_posOp` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comm_momOp_posOp` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterMixedLinearEsa
open BookProof.HermiteProductCore
open BookProof.MixedLinearEsa
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

set_option maxHeartbeats 1000000 in
-- The core-level commutator unfolds a composite of three linear equivalences, which is
-- elaboration-heavy; the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp (i k : Fin d) :
    (momOp i).comp (posOp k) - (posOp k).comp (momOp i)
      = (if i = k then -Complex.I else 0) • LinearMap.id := by sorry
