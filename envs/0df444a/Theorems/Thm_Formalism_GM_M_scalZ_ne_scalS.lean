-- Prove2me | Theorems.Thm_Formalism_GM_M_scalZ_ne_scalS
-- name    : Formalism.GM.M.scalZ_ne_scalS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:52.893146+00:00
-- url     : https://prove2.me/theorems/3f28a7ec-e6f7-4cc9-83bb-38f3bc1d8bd3
-- title:
--   M: scal Z ne scal S
-- statement:
--   The M construction uses the scal Z ne scal S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L428-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L428-L428

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
variable {t : ℕ}

theorem Formalism.GM.M.scalZ_ne_scalS (i k : Fin (t + 1)) : scalZ N r t i ≠ scalS N r t k := by sorry
