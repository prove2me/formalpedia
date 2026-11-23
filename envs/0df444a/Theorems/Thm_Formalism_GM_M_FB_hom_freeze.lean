-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_hom_freeze
-- name    : Formalism.GM.M.FB.hom_freeze
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:48.849794+00:00
-- url     : https://prove2.me/theorems/eec710e7-4524-46fe-aafe-0784e768d200
-- title:
--   FB: hom freeze
-- statement:
--   The FB construction uses the hom freeze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L249-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L249-L257

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
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.hom_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (freeze p LL ρ n f) n := by sorry
