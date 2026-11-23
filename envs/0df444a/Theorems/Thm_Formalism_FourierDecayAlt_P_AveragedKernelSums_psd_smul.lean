-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_smul
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:04.092981+00:00
-- url     : https://prove2.me/theorems/95c60a96-5f88-4f8d-81d5-eccfadb0d6c6
-- title:
--   Averaged Kernel Sums: psd smul
-- statement:
--   The Averaged Kernel Sums construction uses the psd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L17-L31

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_smul {X : Type} (F : Finset X) (k : X → X → ℂ) (c : ℝ) (hc : 0 ≤ c) (h : IsPSD F k) :
    IsPSD F (fun x y => (c : ℂ) * k x y) := by sorry
