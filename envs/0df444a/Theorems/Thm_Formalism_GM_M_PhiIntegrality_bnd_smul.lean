-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_smul
-- name    : Formalism.GM.M.PhiIntegrality.bnd_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:37.034646+00:00
-- url     : https://prove2.me/theorems/6459fa0d-7782-456f-970d-480a4c3ada95
-- title:
--   Phi Integrality: bnd smul
-- statement:
--   The Phi Integrality construction uses the bnd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L44-L49

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}

theorem Formalism.GM.M.PhiIntegrality.bnd_smul {B : ℝ} (a : ℚ_[p]) {u : MvPolynomial σ ℚ_[p]} (h : Bnd B u) :
    Bnd (‖a‖ * B) (a • u) := by sorry
