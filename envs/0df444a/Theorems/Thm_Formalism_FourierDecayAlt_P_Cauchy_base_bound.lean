-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_base_bound
-- name    : Formalism.FourierDecayAlt.P.Cauchy.base_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:59.632808+00:00
-- url     : https://prove2.me/theorems/e48dc3c3-2b2d-4531-b89f-0cf5f06d789d
-- title:
--   Cauchy: base bound
-- statement:
--   The Cauchy construction uses the base bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L63-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L63-L86

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Cauchy
open Complex Metric Set

theorem Formalism.FourierDecayAlt.P.Cauchy.base_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by sorry
