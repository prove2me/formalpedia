-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_hom_aeval
-- name    : Formalism.GM.M.FB.hom_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:02.827138+00:00
-- url     : https://prove2.me/theorems/1dec7a24-dc4a-45c1-b837-00c39c00b6ad
-- title:
--   FB: hom aeval
-- statement:
--   The FB construction uses the hom aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L226-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L226-L247

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

theorem Formalism.GM.M.FB.hom_aeval (LL : Letters N) (ρ : Fin r) (f : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (aeval (freezeSub p LL ρ) f) LL.total := by sorry
