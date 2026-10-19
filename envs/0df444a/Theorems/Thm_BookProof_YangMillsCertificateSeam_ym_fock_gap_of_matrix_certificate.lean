-- Prove2me | Theorems.Thm_BookProof_YangMillsCertificateSeam_ym_fock_gap_of_matrix_certificate
-- name    : BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T13:23:36.142784+00:00
-- url     : https://prove2.me/theorems/1c66c61c-4464-4b08-8c6d-4c1b404c3726
-- title:
--   `BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate` (c : MatrixBoundRecord) (hchk : c.checkBounds = true) (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsCertificateSeam`.
--
--   `BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate` (c : MatrixBoundRecord) (hchk : c.checkBounds = true) (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) c.m → ((c.muQ : ℚ) : ℝ) * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) (hdiag : ∀ i, c.m ≤ i → ((c.dminQ : ℚ) : ℝ) ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re) (hrow : ∀ i, c.m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) → i ∉ S → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((c.rmaxQ : ℚ) : ℝ)) (hblockrow : ∀ i, i < c.m → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((c.epsQ : ℚ) : ℝ)) (hblockcol : ∀ j, c.m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < c.m) → ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ ((c.epsQ : ℚ) : ℝ)) : dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → ((c.lowerQ : ℚ) : ℝ) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate`.

-- Generated from ChapterYangMillsCertificateSeam.lean — theorem BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterSchurGershgorinGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Mathlib
import Definitions.Def_ChapterYangMillsCertificateSeam
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
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

theorem BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate (c : MatrixBoundRecord)
    (hchk : c.checkBounds = true)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) c.m →
      ((c.muQ : ℚ) : ℝ) * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (hdiag : ∀ i, c.m ≤ i →
      ((c.dminQ : ℚ) : ℝ) ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re)
    (hrow : ∀ i, c.m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.rmaxQ : ℚ) : ℝ))
    (hblockrow : ∀ i, i < c.m → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.epsQ : ℚ) : ℝ))
    (hblockcol : ∀ j, c.m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < c.m) →
      ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.epsQ : ℚ) : ℝ)) :
    dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        ((c.lowerQ : ℚ) : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
