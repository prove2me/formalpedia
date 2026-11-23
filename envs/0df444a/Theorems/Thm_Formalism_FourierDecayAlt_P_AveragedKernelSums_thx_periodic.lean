-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_thx_periodic
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_periodic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:19.872956+00:00
-- url     : https://prove2.me/theorems/18b972d8-6de4-42c5-ba13-780dafd53e26
-- title:
--   Averaged Kernel Sums: thx periodic
-- statement:
--   The Averaged Kernel Sums construction uses the thx periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L76-L90

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.thx_periodic (hD : LocalDatum K R ψ) (m : ℕ) (A B : Finset K) (τ : K → Kˣ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hB : ∀ b ∈ B, b ∈ R) (z r : K) (hr : r ∈ R) :
    thx R ψ m cr A B τ (z + r) = thx R ψ m cr A B τ z := by sorry
