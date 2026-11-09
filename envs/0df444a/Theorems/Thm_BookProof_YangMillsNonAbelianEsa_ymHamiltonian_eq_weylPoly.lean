-- Prove2me | Theorems.Thm_BookProof_YangMillsNonAbelianEsa_ymHamiltonian_eq_weylPoly
-- name    : BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:07:17.596697+00:00
-- url     : https://prove2.me/theorems/05567e54-875e-4b24-9d04-a24b7ebfc910
-- title:
--   `BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly` (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ymHamiltonian (coreRepPoly 99) fabc = weylPoly ymIdx (ymMag fabc)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsNonAbelianEsa`.
--
--   `BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly` (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ymHamiltonian (coreRepPoly 99) fabc = weylPoly ymIdx (ymMag fabc)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly`.

-- Generated from ChapterYangMillsNonAbelianEsa.lean — theorem BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Mathlib
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite



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

theorem BookProof.YangMillsNonAbelianEsa.ymHamiltonian_eq_weylPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ymHamiltonian (coreRepPoly 99) fabc = weylPoly ymIdx (ymMag fabc) := by sorry
