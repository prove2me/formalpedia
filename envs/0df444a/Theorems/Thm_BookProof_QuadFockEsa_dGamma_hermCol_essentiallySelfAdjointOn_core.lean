-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_dGamma_hermCol_essentiallySelfAdjointOn_core
-- name    : BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:07:34.403482+00:00
-- url     : https://prove2.me/theorems/830b8987-0e69-4b75-8543-9ef7b03b931c
-- title:
--   `BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hsym : PolySym T) (h : IsBand2 T) : Essenti
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hsym : PolySym T) (h : IsBand2 T) : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (hermCol e T))
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.HermiteBand
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.QuadFockEsa



open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core (e : ℕ ≃ (Fin d →₀ ℕ))
    {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hsym : PolySym T) (h : IsBand2 T) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (hermCol e T)) := by sorry
