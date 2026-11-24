-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_integrable
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:53.530035+00:00
-- url     : https://prove2.me/theorems/8c78829d-3e72-4fcb-97f1-f9efe27a5afc
-- title:
--   Wirtinger Integration By Parts: wir integrable
-- statement:
--   The Wirtinger Integration By Parts construction uses the wir integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L227-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L227-L233

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_integrable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {φ : (Fin d → ℂ) → ℂ} {a : (Fin d → ℂ) → V} {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) (hφ : ContinuousOn φ Ω)
    (ha : Continuous a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    Integrable (fun x => φ x • a x) (volume : Measure (Fin d → ℂ)) := by sorry
