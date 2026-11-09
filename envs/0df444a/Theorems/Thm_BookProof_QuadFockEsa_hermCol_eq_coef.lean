-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_hermCol_eq_coef
-- name    : BookProof.QuadFockEsa.hermCol_eq_coef
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:07:51.629183+00:00
-- url     : https://prove2.me/theorems/00068b52-375b-4e5a-ae26-aabc71438435
-- title:
--   `BookProof.QuadFockEsa.hermCol_eq_coef` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} {f : (Fin d →₀ ℕ) →₀ ℂ} {k : ℕ} (hf : T (hpsi (e k)) = hcomb...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.hermCol_eq_coef` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} {f : (Fin d →₀ ℕ) →₀ ℂ} {k : ℕ} (hf : T (hpsi (e k)) = hcomb f) (j : ℕ) : hermCol e T k j = f (e j)
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.hermCol_eq_coef`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.hermCol_eq_coef
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.HermiteBand
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.QuadFockEsa



open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadFockEsa.hermCol_eq_coef (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    {f : (Fin d →₀ ℕ) →₀ ℂ} {k : ℕ} (hf : T (hpsi (e k)) = hcomb f) (j : ℕ) :
    hermCol e T k j = f (e j) := by sorry
