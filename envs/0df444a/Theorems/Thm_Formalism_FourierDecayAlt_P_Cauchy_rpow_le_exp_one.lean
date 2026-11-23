-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cauchy_rpow_le_exp_one
-- name    : Formalism.FourierDecayAlt.P.Cauchy.rpow_le_exp_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:05.877073+00:00
-- url     : https://prove2.me/theorems/cc872b86-a9ef-4504-87ed-fb73d709ec26
-- title:
--   Cauchy: rpow le exp one
-- statement:
--   The Cauchy construction uses the rpow le exp one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L35-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Cauchy.lean#L35-L61

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

theorem Formalism.FourierDecayAlt.P.Cauchy.rpow_le_exp_one {σ : ℝ} (hσ : 4 ≤ σ) : (1 - 2 * (1 / (4 * σ))) ^ (-σ) ≤ Real.exp 1 := by sorry
