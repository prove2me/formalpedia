-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_sum
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:10.791297+00:00
-- url     : https://prove2.me/theorems/7c346c41-3ec9-463a-82e0-e8d495149439
-- title:
--   Positive Semidefinite Closure: psd sum
-- statement:
--   The Positive Semidefinite Closure construction uses the psd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L34-L42

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_sum {X ι : Type} {F : Finset X} (T : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ T, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ T, k i x y) := by sorry
