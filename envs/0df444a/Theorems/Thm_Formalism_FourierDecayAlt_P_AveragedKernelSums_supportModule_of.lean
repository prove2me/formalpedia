-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_supportModule_of
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.supportModule_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:39.054814+00:00
-- url     : https://prove2.me/theorems/62b6636f-26fb-47ee-ade7-768f4c1c6a10
-- title:
--   Averaged Kernel Sums: support Module of
-- statement:
--   The Averaged Kernel Sums construction uses the support Module of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L126-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L126-L196

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.supportModule_of (hSup : NsSupport) (K : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (R : Subring K) (ψ : AddChar K ℂ) (hL : LocalDatum K R ψ) (s : ℕ)
    (F : Finset (Point K)) (hs : 1 ≤ s) :
    ∃ Lc : Submodule R K, IsCutModule R ψ s F Lc ∧
      ((∀ h ∈ F, InGLR R h) → ∀ x, x ∈ Lc ↔ x ∈ R) := by sorry
