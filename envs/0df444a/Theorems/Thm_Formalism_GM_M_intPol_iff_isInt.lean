-- Prove2me | Theorems.Thm_Formalism_GM_M_intPol_iff_isInt
-- name    : Formalism.GM.M.intPol_iff_isInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:46.053807+00:00
-- url     : https://prove2.me/theorems/0f250193-bbaf-4587-a659-a0aab635f122
-- title:
--   M: int Pol iff is Int
-- statement:
--   The M construction uses the int Pol iff is Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L476-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L476-L490

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
variable {σ : Type}

theorem Formalism.GM.M.intPol_iff_isInt (f : MvPolynomial σ ℚ_[p]) : f ∈ IntPol p σ ↔ IsInt f := by sorry
