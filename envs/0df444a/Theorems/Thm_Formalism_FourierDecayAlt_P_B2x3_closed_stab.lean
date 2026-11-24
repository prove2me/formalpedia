-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closed_stab
-- name    : Formalism.FourierDecayAlt.P.B2x3.closed_stab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:49.624979+00:00
-- url     : https://prove2.me/theorems/28f3f45a-db53-43d7-8184-5bcc04457a15
-- title:
--   B2x3: closed stab
-- statement:
--   The B2x3 construction uses the closed stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L19-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L19-L41

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x3.closed_stab (k r : ℕ) (F : Set (Fin (2 * r + k + 1) → ℂ)) :
    IsClosedSubgroup {g : Mat k r | g ∈ GV k r ∧ ∀ v ∈ F, g *ᵥ v = v} := by sorry
