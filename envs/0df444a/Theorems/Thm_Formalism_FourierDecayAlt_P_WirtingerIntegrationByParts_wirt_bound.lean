-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_bound
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:22.964969+00:00
-- url     : https://prove2.me/theorems/66b54879-7144-44b9-8a88-41117d8af57b
-- title:
--   Wirtinger Integration By Parts: wirt bound
-- statement:
--   The Wirtinger Integration By Parts construction uses the wirt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L704-L711
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L704-L711

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_bound {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) {j : ℕ} (hj : j ≤ n)
    (x : Fin d → ℂ) : ‖iteratedFDeriv ℝ j (wirt k f) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f x‖ := by sorry
