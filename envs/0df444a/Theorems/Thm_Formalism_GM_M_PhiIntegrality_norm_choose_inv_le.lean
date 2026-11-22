-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_choose_inv_le
-- name    : Formalism.GM.M.PhiIntegrality.norm_choose_inv_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:35.511569+00:00
-- url     : https://prove2.me/theorems/69d5e201-a60b-4fd7-87c3-883dd0c7fea5
-- title:
--   Phi Integrality: norm choose inv le
-- statement:
--   The Phi Integrality construction uses the norm choose inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L21-L26

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

theorem Formalism.GM.M.PhiIntegrality.norm_choose_inv_le (j k : ℕ) (hk : k ≤ j) :
    ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (Nat.log p j) := by sorry
