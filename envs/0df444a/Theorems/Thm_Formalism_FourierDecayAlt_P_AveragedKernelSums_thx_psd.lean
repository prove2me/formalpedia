-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thx_psd
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:05.179452+00:00
-- url     : https://prove2.me/theorems/c1f817b0-c08d-4c7c-99d7-62dcd6d8c34e
-- title:
--   Averaged Kernel Sums: thx psd
-- statement:
--   The Averaged Kernel Sums construction uses the thx psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L92-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L92-L122

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_psd (hG : ∀ F' : Finset (Point K × Kˣ), (∀ p ∈ F', ∀ p' ∈ F', p.1.1.sum = p'.1.1.sum) →
      ∀ (m : ℕ) (cr : K ⧸ R.toAddSubgroup → Kˣ), IsCr R cr →
      IsPSD F' (fun p p' => uGram R ψ m cr Set.univ p.1 p'.1 p.2 p'.2))
    (m n₀ : ℕ) (F : Finset (Point K)) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hF : ∀ h ∈ F, h.1.sum = n₀) (hcr : IsCr R cr) (z : K) :
    IsPSD F (thx R ψ m cr A B τ z) := by sorry
