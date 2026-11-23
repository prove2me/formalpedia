-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_scale
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:55.702358+00:00
-- url     : https://prove2.me/theorems/23413965-5d17-4fa4-9cf7-2fdd1119ac9b
-- title:
--   Positive Semidefinite Closure: psd scale
-- statement:
--   The Positive Semidefinite Closure construction uses the psd scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L44-L51

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_scale {X : Type} {F : Finset X} {k : X → X → ℂ} (c : X → ℝ) (hk : IsPSD F k) :
    IsPSD F (fun x y => ((c x * c y : ℝ) : ℂ) * k x y) := by sorry
