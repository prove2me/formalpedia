-- Prove2me | Theorems.Thm_Formalism_GM_M_zmon_eq
-- name    : Formalism.GM.M.zmon_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:14.683122+00:00
-- url     : https://prove2.me/theorems/152cb069-4068-4152-a60a-3d8fd7c7807d
-- title:
--   M: zmon eq
-- statement:
--   The M construction uses the zmon eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L535-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L535-L539

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

theorem Formalism.GM.M.zmon_eq : ((∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) ℚ_[p]) =
      monomial (zmS D) 1 := by sorry
