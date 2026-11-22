-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
-- name    : Formalism.GM.FrozenVariableComponents.etaPart_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:02.50579+00:00
-- url     : https://prove2.me/theorems/103fd820-ae86-41d0-87d8-288dd769f47c
-- title:
--   Frozen Variable Components: eta Part apply
-- statement:
--   The Frozen Variable Components construction uses the eta Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L25-L27

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
variable {N r : ℕ}

theorem Formalism.GM.FrozenVariableComponents.etaPart_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (c : Fin r) :
    etaPart m c = m (Fin.last N, c) := by sorry

attribute [defeq] Formalism.GM.FrozenVariableComponents.etaPart_apply
