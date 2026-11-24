-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wir_hasLineDerivAt
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_hasLineDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:30.809849+00:00
-- url     : https://prove2.me/theorems/64b51070-4e84-48fb-82c1-dcaa0ed0a22d
-- title:
--   Wirtinger Integration By Parts: wir has Line Deriv At
-- statement:
--   The Wirtinger Integration By Parts construction uses the wir has Line Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L235-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L235-L259

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wir_hasLineDerivAt {d : ℕ} (β t : ℂ) {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ}
    (hg : DifferentiableAt ℂ g x) (v : Fin d → ℂ) :
    HasLineDerivAt ℝ (fun y => psi β (g y / t))
      (psi β (g x / t) * (Complex.I * (((β / t * fderiv ℂ g x v).re : ℝ) : ℂ))) x v := by sorry
