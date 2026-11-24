-- Prove2me | Theorems.Thm_Formalism_zetaPrimeSumErrorLipschitz
-- name    : Formalism.zetaPrimeSumErrorLipschitz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:52.993248+00:00
-- url     : https://prove2.me/theorems/9eee42ca-8326-4696-834c-2781a0cffbff
-- title:
--   Formalism: zeta Prime Sum Error Lipschitz
-- statement:
--   The Formalism construction uses the zeta Prime Sum Error Lipschitz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L220-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/GzLipschitz.lean#L220-L235

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open LogFactorialMertensBounds

theorem Formalism.zetaPrimeSumErrorLipschitz : GzLipschitz := by sorry
