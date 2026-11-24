-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_heisG_apply
-- name    : Formalism.FourierDecayAlt.P.B2x4.heisG_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:26:59.598803+00:00
-- url     : https://prove2.me/theorems/d95404ac-9997-4409-9dff-e3441afc4b62
-- title:
--   B2x4: heis G apply
-- statement:
--   The B2x4 construction uses the heis G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L183-L189

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x4.heisG_apply (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) (i j : Fin (2 * (1 + r') + k + 1)) :
    heisG k r' v b i j = (if i = j then 1 else 0) - e0 k r' i * herm (Hpk k (1 + r')) (bvec j) v +
      (v i + b * e0 k r' i) * (if j.val = 2 * (1 + r') + k then 1 else 0) := by sorry
