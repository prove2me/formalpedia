-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_toSm_mulZ
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.toSm_mulZ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:22:24.295991+00:00
-- url     : https://prove2.me/theorems/36f953c4-c2a7-4cf7-b574-67b265c80735
-- title:
--   GC: to Sm mul Z
-- statement:
--   The GC construction uses the to Sm mul Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L76-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L76-L97

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.toSm_mulZ (P : M.Par) {v w : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P))
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ann P)) (hvw : ∀ ζ ∈ Ann P, w ζ * v ζ = 1)
    (g : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (fun q => v q.1.2 * g q) = fnZ P v * MA.toSm P g := by sorry
