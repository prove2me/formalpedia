-- Prove2me | Theorems.Thm_Formalism_GM_M_xiVar_inj
-- name    : Formalism.GM.M.xiVar_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:33.766409+00:00
-- url     : https://prove2.me/theorems/80d38e14-68ee-4fcd-9ec8-a749ade9b6d8
-- title:
--   M: xi Var inj
-- statement:
--   The M construction uses the xi Var inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L705-L706
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L705-L706

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)

theorem Formalism.GM.M.xiVar_inj : Function.Injective (xiVar N r D.T.t) := by sorry
