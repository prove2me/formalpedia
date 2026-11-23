-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_congr
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:33.700831+00:00
-- url     : https://prove2.me/theorems/f6a8e906-c77a-4e75-9cde-8c39ec07df8c
-- title:
--   Positive Semidefinite Closure: psd congr
-- statement:
--   The Positive Semidefinite Closure construction uses the psd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L16-L21

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_congr {X : Type} {F : Finset X} {k k' : X → X → ℂ}
    (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : IsPSD F k) : IsPSD F k' := by sorry
