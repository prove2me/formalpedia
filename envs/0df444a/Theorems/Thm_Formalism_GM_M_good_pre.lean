-- Prove2me | Theorems.Thm_Formalism_GM_M_good_pre
-- name    : Formalism.GM.M.good_pre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:29.596007+00:00
-- url     : https://prove2.me/theorems/57e2ef41-fb9e-4a97-b6f2-775545dc14f6
-- title:
--   M: good pre
-- statement:
--   The M construction uses the good pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L544-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L544-L551

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

theorem Formalism.GM.M.good_pre (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∃ s, Good (scalS N r D.T.t) (pre (p := p) (r := r) D j jp) (lv j jp) s := by sorry
