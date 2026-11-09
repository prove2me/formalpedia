-- Prove2me | Theorems.Thm_BookProof_YangMillsNonAbelianEsa_one_le_polyW_weylPotPoly
-- name    : BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T21:05:32.818183+00:00
-- url     : https://prove2.me/theorems/8e2c57a2-a6f7-4b34-ab4a-f6cdac1cd309
-- title:
--   `BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly` {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) (x : Vd d) : 1 ≤ polyW (weylPotPoly Φ) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsNonAbelianEsa`.
--
--   `BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly` {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) (x : Vd d) : 1 ≤ polyW (weylPotPoly Φ) x
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly`.

-- Generated from ChapterYangMillsNonAbelianEsa.lean — theorem BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly
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

theorem BookProof.YangMillsNonAbelianEsa.one_le_polyW_weylPotPoly {Φ : Fin r → MvPolynomial (Fin d) ℂ}
    (hΦ : ∀ j, RealCoeff (Φ j)) (x : Vd d) : 1 ≤ polyW (weylPotPoly Φ) x := by sorry
