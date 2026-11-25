-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_qminor_val
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_qminor_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:32.830445+00:00
-- url     : https://prove2.me/theorems/0704892e-d77c-5e19-8465-ac3063a37228
-- title:
--   GC: jet T qminor val
-- statement:
--   The GC construction uses the jet T qminor val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L181-L185

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_qminor_val {t : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (hZ : ZJ k r (Q.mdim k r (Fin.last r)) f g₀) (c d : Fin t → Fin (Q.mdim k r (Fin.last r))) (u : ℂ)
    (ht : t ≤ Q.mdim k r (Fin.last r)) :
    qminorOp (Q.EH k r) (Q.posL k r (Fin.last r) ∘ c) (Q.posL k r (Fin.last r) ∘ d) u f g₀ = 0 := by sorry
