-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
-- name    : Formalism.GM.FrozenVariableComponents.comb_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:44.229792+00:00
-- url     : https://prove2.me/theorems/9d1bb661-2d52-43ed-a9ec-d14cb4189d37
-- title:
--   Frozen Variable Components: comb cast Succ
-- statement:
--   The Frozen Variable Components construction uses the comb cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L29-L31

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

theorem Formalism.GM.FrozenVariableComponents.comb_castSucc (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) (i : Fin N) (c : Fin r) :
    comb b m (Fin.castSucc i, c) = m (i, c) := by sorry
