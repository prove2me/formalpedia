-- Prove2me | Theorems.Thm_Formalism_GM_M_inl_ne_scalS
-- name    : Formalism.GM.M.inl_ne_scalS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:30.125101+00:00
-- url     : https://prove2.me/theorems/162f1b78-97fb-4a7c-8449-444074020577
-- title:
--   M: inl ne scal S
-- statement:
--   The M construction uses the inl ne scal S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L430-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L430-L431

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

theorem Formalism.GM.M.inl_ne_scalS (x : Fin (N + 1) × Fin r) (k : Fin (t + 1)) : (Sum.inl x : BVar N r t) ≠ scalS N r t k := by sorry
