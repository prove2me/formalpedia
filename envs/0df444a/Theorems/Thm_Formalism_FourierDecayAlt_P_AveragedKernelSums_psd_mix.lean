-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_mix
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_mix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:45.640375+00:00
-- url     : https://prove2.me/theorems/33d71f25-c709-4d48-b45a-a20ff4ead05d
-- title:
--   Averaged Kernel Sums: psd mix
-- statement:
--   The Averaged Kernel Sums construction uses the psd mix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L47-L65

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_mix {X Y : Type} (F : Finset X) (B : Finset Y) (e : Y → ℂ)
    (k : X × Y → X × Y → ℂ) (h : IsPSD (F ×ˢ B) k) :
    IsPSD F (fun x x' => ∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (x', b')) := by sorry
