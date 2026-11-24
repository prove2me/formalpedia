-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_vLet_mem
-- name    : Formalism.FourierDecayAlt.P.PBG.vLet_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:52.270932+00:00
-- url     : https://prove2.me/theorems/8788e3f7-0b1e-4d4b-a786-fa1f4d1dee52
-- title:
--   PBG: v Let mem
-- statement:
--   The PBG construction uses the v Let mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L463-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L463-L542

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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r)

theorem Formalism.FourierDecayAlt.P.PBG.vLet_mem (l : C.Letter) (e : Fin 2) (h : Wsm (E := E) (Sd z z' j hj)) :
    D.vLet k r z z' j hj l e h.1 ∈ Wsm (E := E) (Sd z z' j hj) := by sorry
