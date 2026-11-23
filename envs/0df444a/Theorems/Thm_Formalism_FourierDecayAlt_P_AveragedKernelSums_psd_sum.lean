-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_psd_sum
-- name    : Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:56.67128+00:00
-- url     : https://prove2.me/theorems/90a1134a-f101-41a6-90b6-dc829d0a32c9
-- title:
--   Averaged Kernel Sums: psd sum
-- statement:
--   The Averaged Kernel Sums construction uses the psd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean#L33-L45

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

theorem Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_sum {X ι : Type} (F : Finset X) (s : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ s, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ s, k i x y) := by sorry
