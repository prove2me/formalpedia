-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hb_form
-- name    : Formalism.FourierDecayAlt.P.B2x3.hb_form
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:31.644794+00:00
-- url     : https://prove2.me/theorems/772c6500-e368-45d4-bc8a-fd8329fbb3de
-- title:
--   B2x3: hb form
-- statement:
--   The B2x3 construction uses the hb form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L659-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L659-L667

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

theorem Formalism.FourierDecayAlt.P.B2x3.hb_form (v w : Fin (k + 1) → ℂ) :
    star w ⬝ᵥ (Hb k *ᵥ v) =
      (∑ i : Fin k, star (w i.castSucc) * v i.castSucc) - star (w (Fin.last k)) * v (Fin.last k) := by sorry
