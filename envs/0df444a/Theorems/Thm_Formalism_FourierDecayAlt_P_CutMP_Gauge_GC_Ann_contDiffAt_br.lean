-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_contDiffAt_br
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.contDiffAt_br
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:50.945116+00:00
-- url     : https://prove2.me/theorems/ef7c1633-91eb-5c62-baaa-55a38f2efdc8
-- title:
--   Ann: cont Diff At br
-- statement:
--   The Ann construction uses the cont Diff At br property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NeZeroOfAn.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NeZeroOfAn.lean#L71-L74

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by sorry
