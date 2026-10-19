-- Prove2me | Theorems.Thm_BookProof_SchurGershgorin_ym_fock_gap_of_truncated_gap_and_matrix_bounds
-- name    : BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T13:23:20.877977+00:00
-- url     : https://prove2.me/theorems/1a347b2b-b60d-467d-9301-4891b3692c43
-- title:
--   `BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds` {m : ℕ} {mu eps : ℝ} (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps) (d r : ℕ → ℝ) (htrunc : ∀ x : finiteModeDom
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurGershgorinGap`.
--
--   `BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds` {m : ℕ} {mu eps : ℝ} (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps) (d r : ℕ → ℝ) (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) (hdiag : ∀ i, m ≤ i → d i ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re) (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ r i) (hgap : ∀ i, m ≤ i → mu ≤ d i - r i) (hblockrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps) (hblockcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) → ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps) : dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → (mu - eps) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds`.

-- Generated from ChapterSchurGershgorinGap.lean — theorem BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Mathlib
import Definitions.Def_ChapterSchurGershgorinGap
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
open BookProof.SchurGershgorin


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

theorem BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps) (d r : ℕ → ℝ)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) m →
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (hdiag : ∀ i, m ≤ i →
      d i ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (hblockrow : ∀ i, i < m → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps)
    (hblockcol : ∀ j, m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < m) →
      ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖ ≤ eps) :
    dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (mu - eps) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
