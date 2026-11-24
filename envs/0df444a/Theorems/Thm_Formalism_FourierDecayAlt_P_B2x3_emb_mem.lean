-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mem
-- name    : Formalism.FourierDecayAlt.P.B2x3.emb_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:54:46.229668+00:00
-- url     : https://prove2.me/theorems/90739532-cb1c-4b6c-b097-b8105cefdb80
-- title:
--   B2x3: emb mem
-- statement:
--   The B2x3 construction uses the emb mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L482-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L482-L491

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.emb_mem (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r a ∈ GV k r ↔ aᴴ * Hb k * a = Hb k := by sorry
