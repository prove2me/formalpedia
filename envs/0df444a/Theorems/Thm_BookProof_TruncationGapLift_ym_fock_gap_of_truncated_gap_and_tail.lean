-- Prove2me | Theorems.Thm_BookProof_TruncationGapLift_ym_fock_gap_of_truncated_gap_and_tail
-- name    : BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:22:38.784085+00:00
-- url     : https://prove2.me/theorems/19eaf6dd-ae00-47b5-9bde-39301e65a12f
-- title:
--   `BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail` {m : ℕ} {mu eps : ℝ} (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps) (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTruncationGapLift`.
--
--   `BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail` {m : ℕ} {mu eps : ℝ} (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps) (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) (htail : ∀ w : finiteModeDomain (coreBasis e), (w : L2d 99) ∈ tailSpan (coreBasis e) m → mu * ‖(w : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) w) (hcoup : ∀ x w : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → (w : L2d 99) ∈ tailSpan (coreBasis e) m → |(inner ℂ (x : L2d 99) (ymHamiltonian (coreRepBasis e) fabc w) : ℂ).re| ≤ eps * ‖(x : L2d 99)‖ * ‖(w : L2d 99)‖) : dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → (mu - eps) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail`.

-- Generated from ChapterTruncationGapLift.lean — theorem BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
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
open BookProof.TruncationGapLift


noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {D : Submodule ℂ F}
variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

theorem BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) m →
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (htail : ∀ w : finiteModeDomain (coreBasis e), (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      mu * ‖(w : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) w)
    (hcoup : ∀ x w : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      |(inner ℂ (x : L2d 99) (ymHamiltonian (coreRepBasis e) fabc w) : ℂ).re|
        ≤ eps * ‖(x : L2d 99)‖ * ‖(w : L2d 99)‖) :
    dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (mu - eps) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
