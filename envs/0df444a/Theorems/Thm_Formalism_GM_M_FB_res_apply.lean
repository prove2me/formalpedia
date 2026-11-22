-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_res_apply
-- name    : Formalism.GM.M.FB.res_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:34.877652+00:00
-- url     : https://prove2.me/theorems/125cc5f5-9a5c-4772-b71f-facd8ab69d2e
-- title:
--   FB: res apply
-- statement:
--   The FB construction uses the res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L45-L47

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.res_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (v : Fin N × Fin r) :
    res m v = m (Fin.castSucc v.1, v.2) := by sorry
