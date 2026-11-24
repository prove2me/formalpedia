-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_base_bound
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.base_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:49.354516+00:00
-- url     : https://prove2.me/theorems/6366a969-cec1-4786-a246-68c0f63232d7
-- title:
--   Wirtinger Integration By Parts: base bound
-- statement:
--   The Wirtinger Integration By Parts construction uses the base bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L713-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L713-L726

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.base_bound (β t : ℂ) (g : (Fin d → ℂ) → ℂ) {S : ℝ} {a : (Fin d → ℂ) → V} (hc : HasCompactSupport a)
    (hb : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤ S * (muPi β (Fin d) (tsupport a)).toReal := by sorry
