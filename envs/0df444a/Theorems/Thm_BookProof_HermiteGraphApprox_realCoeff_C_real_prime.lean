-- Prove2me | Theorems.Thm_BookProof_HermiteGraphApprox_realCoeff_C_real_prime
-- name    : BookProof.HermiteGraphApprox.realCoeff_C_real_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T20:42:27.996748+00:00
-- url     : https://prove2.me/theorems/ea1b99c0-d585-4f7a-bd4e-bff3fbabda1e
-- title:
--   BookProof.HermiteGraphApprox.realCoeff_C_real'
-- statement:
--   BookProof.HermiteGraphApprox.realCoeff_C_real'

-- Generated from ChapterHermiteGraphApprox.lean — theorem BookProof.HermiteGraphApprox.realCoeff_C_real'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterConvolutionCalc
import Mathlib
import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteLadderShift
open BookProof.YangMillsHermite



open MeasureTheory SchwartzMap MvPolynomial Filter Topology
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.DegEnergy BookProof.HermiteLadder
open BookProof.ConvolutionCalc
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteGraphApprox.realCoeff_C_real_prime (c : ℝ) : RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) := by sorry
