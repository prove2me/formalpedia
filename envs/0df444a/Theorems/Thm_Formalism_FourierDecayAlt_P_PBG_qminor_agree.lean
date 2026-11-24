-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_qminor_agree
-- name    : Formalism.FourierDecayAlt.P.PBG.qminor_agree
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:20:00.547637+00:00
-- url     : https://prove2.me/theorems/fb25bbdc-44ba-4e90-a7b3-3b41e03292c3
-- title:
--   PBG: qminor agree
-- statement:
--   The PBG construction uses the qminor agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L203-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L203-L229

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
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem Formalism.FourierDecayAlt.P.PBG.qminor_agree {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Wsm (E := E) U₀) (g : Mat k r)
    (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    ((qminor (fun a b => EHt (E := E) U₀ hU₀ a b) a b u) f).1 g = qminorOp (EabH (Hpk k r)) a b u f.1 g := by sorry
