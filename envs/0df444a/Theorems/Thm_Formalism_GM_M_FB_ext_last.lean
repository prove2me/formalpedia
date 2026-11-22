-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_ext_last
-- name    : Formalism.GM.M.FB.ext_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:28.725408+00:00
-- url     : https://prove2.me/theorems/274e2108-8f2e-4f21-8982-59879f4a8d69
-- title:
--   FB: ext last
-- statement:
--   The FB construction uses the ext last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L53-L55

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

theorem Formalism.GM.M.FB.ext_last (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    ext n ρ m (Fin.last N, c) = if c = ρ then n else 0 := by sorry
