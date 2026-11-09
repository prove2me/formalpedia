-- Prove2me | Theorems.Thm_BookProof_YangMillsNonAbelianEsa_sum_momOp_eq_kinPolyS
-- name    : BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:09:36.627234+00:00
-- url     : https://prove2.me/theorems/112411e1-0620-4b5f-b768-bd60661119ab
-- title:
--   `BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS` {idx : Fin k → Fin d} (hidx : Function.Injective idx) (p : MvPolynomial (Fin d) ℂ) : (∑ m : Fin k, momOp (idx m) (momOp (id
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsNonAbelianEsa`.
--
--   `BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS` {idx : Fin k → Fin d} (hidx : Function.Injective idx) (p : MvPolynomial (Fin d) ℂ) : (∑ m : Fin k, momOp (idx m) (momOp (idx m) p)) = kinPolyS (Finset.image idx Finset.univ) p
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS`.

-- Generated from ChapterYangMillsNonAbelianEsa.lean — theorem BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS
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
variable {d k r : ℕ}

theorem BookProof.YangMillsNonAbelianEsa.sum_momOp_eq_kinPolyS {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    (p : MvPolynomial (Fin d) ℂ) :
    (∑ m : Fin k, momOp (idx m) (momOp (idx m) p)) = kinPolyS (Finset.image idx Finset.univ) p := by sorry
