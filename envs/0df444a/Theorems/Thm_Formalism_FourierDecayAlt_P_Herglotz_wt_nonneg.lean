-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_nonneg
-- name    : Formalism.FourierDecayAlt.P.Herglotz.wt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:35.421401+00:00
-- url     : https://prove2.me/theorems/cde703b2-b896-46be-935d-5afb9f928dce
-- title:
--   Herglotz: wt nonneg
-- statement:
--   The Herglotz construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean#L113-L114

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.Herglotz.wt_nonneg (N : ℕ) (τ : Fin d → ℤ) : 0 ≤ wt N τ := by sorry
