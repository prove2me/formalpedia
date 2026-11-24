-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_natCast_inv_le
-- name    : Formalism.GM.M.PhiIntegrality.norm_natCast_inv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:06.926471+00:00
-- url     : https://prove2.me/theorems/5b41612d-14c2-4df7-9a55-ebdbd1854004
-- title:
--   Phi Integrality: norm nat Cast inv le
-- statement:
--   The Phi Integrality construction uses the norm nat Cast inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L12-L19

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

theorem Formalism.GM.M.PhiIntegrality.norm_natCast_inv_le (n : ℕ) (hn : n ≠ 0) :
    ‖((n : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (n.factorization p) := by sorry
