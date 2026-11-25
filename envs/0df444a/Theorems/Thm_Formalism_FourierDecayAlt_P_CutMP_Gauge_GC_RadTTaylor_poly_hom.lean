-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_poly_hom
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.poly_hom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:02.600036+00:00
-- url     : https://prove2.me/theorems/82fcd426-995d-5b67-a89d-609b9aa1d1ad
-- title:
--   Rad TTaylor: poly hom
-- statement:
--   The Rad TTaylor construction uses the poly hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L123-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L123-L155

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.poly_hom {j i : ℕ} (hij : i ≠ j) (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) W) :
    iteratedFDeriv ℝ i (fun ζ => m (fun _ => ζ)) 0 = 0 := by sorry
