-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_out_sub_mem
-- name    : Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.out_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:23.935814+00:00
-- url     : https://prove2.me/theorems/f80c4a2e-da67-45bd-b475-e0ac5a3909b1
-- title:
--   Positive Semidefinite Closure: out sub mem
-- statement:
--   The Positive Semidefinite Closure construction uses the out sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean#L63-L68

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

theorem Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.out_sub_mem {K : Type} [CommRing K] (Λ : AddSubgroup K) (z : K) :
    (Quotient.out ((z : K) : K ⧸ Λ) : K) - z ∈ Λ := by sorry
