-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_lin_shift
-- name    : Formalism.FourierDecayAlt.P.RuleSS.lin_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:12.071605+00:00
-- url     : https://prove2.me/theorems/07e592ce-07b6-444e-9945-d9943adcd03d
-- title:
--   Rule SS: lin shift
-- statement:
--   The Rule SS construction uses the lin shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L155-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L155-L164

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
omit L

theorem Formalism.FourierDecayAlt.P.RuleSS.lin_shift (n z S : A) (c c' e : ℂ) (hn : n * S = S * n + algebraMap ℂ A e * (z * S))
    (hz : z * S = S * z) (hc : c' = c + e) :
    (-n - algebraMap ℂ A c * z) * S = S * (-n - algebraMap ℂ A c' * z) := by sorry
