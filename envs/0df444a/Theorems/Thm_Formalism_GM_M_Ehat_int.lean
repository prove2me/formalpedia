-- Prove2me | Theorems.Thm_Formalism_GM_M_Ehat_int
-- name    : Formalism.GM.M.Ehat_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:01.609156+00:00
-- url     : https://prove2.me/theorems/516faccf-30f0-4451-9c24-ba42d56424dc
-- title:
--   M: Ehat int
-- statement:
--   The M construction uses the Ehat int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L673-L676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L673-L676

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

theorem Formalism.GM.M.Ehat_int (i : Fin D.T.t) : D.Ehat p (r := r) i ∈ IntPol p (BVar N r D.T.t) := by sorry
