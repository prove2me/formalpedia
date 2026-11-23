-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thxSum_core
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.thxSum_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:35.831095+00:00
-- url     : https://prove2.me/theorems/cb9ef8bb-9bcb-4447-b919-957ebf7fdc89
-- title:
--   Averaged Kernel Sums: thx Sum core
-- statement:
--   The Averaged Kernel Sums construction uses the thx Sum core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L332-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L332-L422

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
open Classical

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.thxSum_core (hL : LocalDatum K R ψ) {L₁ : AddSubgroup K} (hle : L₁ ≤ R.toAddSubgroup)
    (A B : Finset K) (hB : IsReps B R.toAddSubgroup L₁) (hpp : perp ψ (perp ψ L₁) = L₁)
    (hfin : R.toAddSubgroup.relIndex (perp ψ L₁) ≠ 0)
    (hvol : volL R L₁ * volL R (perp ψ L₁) = 1) (m : ℕ) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (h h' : Point K) :
    ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (Quotient.out x : K) ∈ perp ψ L₁ then
        thx R ψ m cr A B τ (Quotient.out x) h h' else 0) =
      ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ ρ ∈ A, ∑ b ∈ B,
        uGram R ψ m cr Set.univ h h' (τ (ρ + b)) (τ (ρ + b)) := by sorry
