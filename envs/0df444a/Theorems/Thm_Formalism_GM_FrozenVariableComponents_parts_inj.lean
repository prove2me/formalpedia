-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_parts_inj
-- name    : Formalism.GM.FrozenVariableComponents.parts_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:25.540843+00:00
-- url     : https://prove2.me/theorems/347a5135-c54a-48b4-898e-da2b07756b4a
-- title:
--   Frozen Variable Components: parts inj
-- statement:
--   The Frozen Variable Components construction uses the parts inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L91-L98

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

theorem Formalism.GM.FrozenVariableComponents.parts_inj {m m' : Fin (N + 1) × Fin r →₀ ℕ} (h1 : etaPart m = etaPart m')
    (h2 : llPart m = llPart m') : m = m' := by sorry
