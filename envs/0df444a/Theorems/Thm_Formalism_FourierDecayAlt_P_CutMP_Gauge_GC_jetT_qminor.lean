-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_qminor
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_qminor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:17:06.502739+00:00
-- url     : https://prove2.me/theorems/804d977c-14eb-4a46-b788-51b786f1577c
-- title:
--   GC: jet T qminor
-- statement:
--   The GC construction uses the jet T qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L152-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L152-L179

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_qminor {N t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (c d : Fin t → Fin (Q.mdim k r (Fin.last r)))
    (u : ℂ) (h : ZJ k r (N + t) f g₀) :
    ZJ k r N (qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f) g₀ := by sorry
