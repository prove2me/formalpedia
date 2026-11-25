-- Prove2me | Theorems.Thm_Formalism_GM_M_SSZ_int
-- name    : Formalism.GM.M.SSZ_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:41.002328+00:00
-- url     : https://prove2.me/theorems/56af9dfd-b4a2-4d4a-b02b-e166f6e3d52a
-- title:
--   M: SSZ int
-- statement:
--   The M construction uses the SSZ int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L683-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L683-L696

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

theorem Formalism.GM.M.SSZ_int (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hx : x ∈ D.SSZ p (r := r)) :
    x ∈ IntPol p (BVar N r D.T.t) := by sorry
