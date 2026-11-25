-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_Top
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_Top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:03.532407+00:00
-- url     : https://prove2.me/theorems/0bde6b07-8a8c-4758-bc9d-cefce23aabc6
-- title:
--   GC: jet T Top
-- statement:
--   The GC construction uses the jet T Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L119-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L119-L134

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_Top {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (u : ℂ) (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by sorry
