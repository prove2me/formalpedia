-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_symm_equiv_hermBasisN
-- name    : BookProof.QuadFockEsa.symm_equiv_hermBasisN
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:06:46.091709+00:00
-- url     : https://prove2.me/theorems/94a06951-64bb-4f5a-b060-aede4d700763
-- title:
--   `BookProof.QuadFockEsa.symm_equiv_hermBasisN` (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) : (coreRepHerm e).equiv.symm ⟨hermBasisN e k, Submodule.subset_span ⟨k, rfl⟩⟩ = hpsi (e k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.symm_equiv_hermBasisN` (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) : (coreRepHerm e).equiv.symm ⟨hermBasisN e k, Submodule.subset_span ⟨k, rfl⟩⟩ = hpsi (e k)
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.symm_equiv_hermBasisN`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.symm_equiv_hermBasisN
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.HermiteBand
open BookProof.HermiteGalerkin
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

theorem BookProof.QuadFockEsa.symm_equiv_hermBasisN (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) :
    (coreRepHerm e).equiv.symm ⟨hermBasisN e k, Submodule.subset_span ⟨k, rfl⟩⟩ = hpsi (e k) := by sorry
