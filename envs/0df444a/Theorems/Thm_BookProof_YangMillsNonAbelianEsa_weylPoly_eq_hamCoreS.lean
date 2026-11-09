-- Prove2me | Theorems.Thm_BookProof_YangMillsNonAbelianEsa_weylPoly_eq_hamCoreS
-- name    : BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:05:43.814596+00:00
-- url     : https://prove2.me/theorems/f765baeb-bbdd-400b-80d5-b2bb14315e8e
-- title:
--   `BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS` {idx : Fin k → Fin d} (hidx : Function.Injective idx) {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) : wey
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsNonAbelianEsa`.
--
--   `BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS` {idx : Fin k → Fin d} (hidx : Function.Injective idx) {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) : weylPoly idx Φ = (((1 / 2 : ℝ)) : ℂ) • hamCoreS (polyW (weylPotPoly Φ)) (continuous_polyW _) (expBounded_polyW _) (Finset.image idx Finset.univ) + (((-1 / 2 : ℝ)) : ℂ) • (polyGaussCore (d := d)).subtype
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS`.

-- Generated from ChapterYangMillsNonAbelianEsa.lean — theorem BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Mathlib
import Definitions.Def_ChapterYangMillsNonAbelianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterF7
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgHermiteFriedrichs
open BookProof.YangMillsFriedrichs
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

theorem BookProof.YangMillsNonAbelianEsa.weylPoly_eq_hamCoreS {idx : Fin k → Fin d} (hidx : Function.Injective idx)
    {Φ : Fin r → MvPolynomial (Fin d) ℂ} (hΦ : ∀ j, RealCoeff (Φ j)) :
    weylPoly idx Φ
      = (((1 / 2 : ℝ)) : ℂ) • hamCoreS (polyW (weylPotPoly Φ)) (continuous_polyW _)
          (expBounded_polyW _) (Finset.image idx Finset.univ)
        + (((-1 / 2 : ℝ)) : ℂ) • (polyGaussCore (d := d)).subtype := by sorry
