-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
-- name    : Formalism.GM.FrozenVariableComponents.llPart_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:13.277078+00:00
-- url     : https://prove2.me/theorems/9d6bde92-8f0b-4a80-997b-5ad183005e82
-- title:
--   Frozen Variable Components: ll Part apply
-- statement:
--   The Frozen Variable Components construction uses the ll Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L21-L23

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

theorem Formalism.GM.FrozenVariableComponents.llPart_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (x : Fin N × Fin r) :
    llPart m x = m (Fin.castSucc x.1, x.2) := by sorry

attribute [defeq] Formalism.GM.FrozenVariableComponents.llPart_apply
