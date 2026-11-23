-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_emb_inj
-- name    : Formalism.GM.FrozenVariableComponents.emb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:32.74946+00:00
-- url     : https://prove2.me/theorems/f6dd40e9-29ef-42a8-b0d4-debb5dc0aa45
-- title:
--   Frozen Variable Components: emb inj
-- statement:
--   The Frozen Variable Components construction uses the emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L688-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L688-L690

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
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.FrozenVariableComponents.emb_inj : Function.Injective (emb : Fin N × Fin r → Fin (N + 1) × Fin r) := by sorry
