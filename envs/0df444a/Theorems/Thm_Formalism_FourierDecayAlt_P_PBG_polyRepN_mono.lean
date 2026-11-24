-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_polyRepN_mono
-- name    : Formalism.FourierDecayAlt.P.PBG.polyRepN_mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:55.0118+00:00
-- url     : https://prove2.me/theorems/a2bbd21c-24a1-438e-9ac1-1cb769862ea4
-- title:
--   PBG: poly Rep N mono
-- statement:
--   The PBG construction uses the poly Rep N mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L34-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L34-L50

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem Formalism.FourierDecayAlt.P.PBG.polyRepN_mono {d d' : ℕ} (hdd : d ≤ d') {f : ℂ → E} {top : E} (h : PolyRepN d f top) :
    PolyRepN d' f (if d = d' then top else 0) := by sorry
