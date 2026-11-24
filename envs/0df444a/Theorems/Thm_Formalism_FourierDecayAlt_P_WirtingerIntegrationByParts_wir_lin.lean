-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_lin
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:33.671802+00:00
-- url     : https://prove2.me/theorems/ea3c049f-a7e1-495e-9565-ffb33570958c
-- title:
--   Wirtinger Integration By Parts: wir lin
-- statement:
--   The Wirtinger Integration By Parts construction uses the wir lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L301-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L301-L306

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_lin {α V : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F₁ F₂ : α → V) (c₁ c₂ : ℂ) (h₁ : Integrable F₁ μ) (h₂ : Integrable F₂ μ) :
    ∫ x, (c₁ • F₁ x - c₂ • F₂ x) ∂μ = c₁ • ∫ x, F₁ x ∂μ - c₂ • ∫ x, F₂ x ∂μ := by sorry
