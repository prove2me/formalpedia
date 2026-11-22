-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
-- name    : Formalism.GM.M.FB.ext_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:14.534348+00:00
-- url     : https://prove2.me/theorems/7a7258a3-6efe-4178-86a5-ac106267755c
-- title:
--   FB: ext cast Succ
-- statement:
--   The FB construction uses the ext cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L57-L59

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

theorem Formalism.GM.M.FB.ext_castSucc (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    ext n ρ m (Fin.castSucc i, c) = m (i, c) := by sorry
