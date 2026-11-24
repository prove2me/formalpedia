-- Prove2me | Theorems.Thm_Formalism_GM_M_chainEmb_inj
-- name    : Formalism.GM.M.chainEmb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:28.510807+00:00
-- url     : https://prove2.me/theorems/ec31bb00-1c13-4448-b694-dd83a53920bf
-- title:
--   M: chain Emb inj
-- statement:
--   The M construction uses the chain Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L698-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L698-L703

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

theorem Formalism.GM.M.chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by sorry
