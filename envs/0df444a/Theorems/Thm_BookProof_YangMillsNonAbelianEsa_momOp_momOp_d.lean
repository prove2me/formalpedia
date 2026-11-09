-- Prove2me | Theorems.Thm_BookProof_YangMillsNonAbelianEsa_momOp_momOp_d
-- name    : BookProof.YangMillsNonAbelianEsa.momOp_momOp_d
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:06:58.934657+00:00
-- url     : https://prove2.me/theorems/58a35d44-b717-4ff6-80d0-0e37a65dea4e
-- title:
--   `BookProof.YangMillsNonAbelianEsa.momOp_momOp_d` (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : momOp j (momOp j p) = -coreD j (coreD j p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsNonAbelianEsa`.
--
--   `BookProof.YangMillsNonAbelianEsa.momOp_momOp_d` (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : momOp j (momOp j p) = -coreD j (coreD j p)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsNonAbelianEsa.momOp_momOp_d`.

-- Generated from ChapterYangMillsNonAbelianEsa.lean — theorem BookProof.YangMillsNonAbelianEsa.momOp_momOp_d
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Mathlib
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgHermiteFriedrichs



open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa
open BookProof.TensorCore BookProof.DirectSumEsa BookProof.SecondQuantizationCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {D : Submodule ℂ F}
variable {d : ℕ}

theorem BookProof.YangMillsNonAbelianEsa.momOp_momOp_d (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j (momOp j p) = -coreD j (coreD j p) := by sorry
