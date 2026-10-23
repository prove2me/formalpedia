-- Prove2me | Theorems.Thm_BookProof_YangMillsCertificateSeam_example_ym_fock_mass_gap
-- name    : BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T13:23:56.243676+00:00
-- url     : https://prove2.me/theorems/572a48d9-30ba-4f6f-a77b-bf8d6b2e5fd4
-- title:
--   `BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap` (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) exampleRecord.m → ((exampleR
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsCertificateSeam`.
--
--   `BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap` (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) exampleRecord.m → ((exampleRecord.muQ : ℚ) : ℝ) * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) (hdiag : ∀ i, exampleRecord.m ≤ i → ((exampleRecord.dminQ : ℚ) : ℝ) ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re) (hrow : ∀ i, exampleRecord.m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, exampleRecord.m ≤ j) → i ∉ S → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((exampleRecord.rmaxQ : ℚ) : ℝ)) (hblockrow : ∀ i, i < exampleRecord.m → ∀ S : Finset ℕ, (∀ j ∈ S, exampleRecord.m ≤ j) → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((exampleRecord.epsQ : ℚ) : ℝ)) (hblockcol : ∀ j, exampleRecord.m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < exampleRecord.m) → ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((exampleRecord.epsQ : ℚ) : ℝ)) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧ dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → u ≠ 0 → 0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap`.

-- Generated from ChapterYangMillsCertificateSeam.lean — theorem BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap
import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterSchurGershgorinGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterYangMillsFockGapChain
import Mathlib
import Definitions.Def_ChapterYangMillsCertificateSeam
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.YangMillsCertificateSeam


noncomputable section


open BookProof.SirkCertificateReader
open BookProof.SchurGershgorin
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

theorem BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap
    (htrunc : ∀ x : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) exampleRecord.m →
      ((exampleRecord.muQ : ℚ) : ℝ) * ‖(x : L2d 99)‖ ^ 2
        ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (hdiag : ∀ i, exampleRecord.m ≤ i →
      ((exampleRecord.dminQ : ℚ) : ℝ)
        ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re)
    (hrow : ∀ i, exampleRecord.m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, exampleRecord.m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((exampleRecord.rmaxQ : ℚ) : ℝ))
    (hblockrow : ∀ i, i < exampleRecord.m → ∀ S : Finset ℕ, (∀ j ∈ S, exampleRecord.m ≤ j) →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((exampleRecord.epsQ : ℚ) : ℝ))
    (hblockcol : ∀ j, exampleRecord.m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < exampleRecord.m) →
      ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((exampleRecord.epsQ : ℚ) : ℝ)) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
