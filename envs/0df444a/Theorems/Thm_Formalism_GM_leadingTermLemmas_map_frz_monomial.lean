-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_map_frz_monomial
-- name    : Formalism.GM.leadingTermLemmas.map_frz_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:16.163705+00:00
-- url     : https://prove2.me/theorems/52fb3552-7f26-4882-a63b-0b13a59eeeee
-- title:
--   leading Term Lemmas: map frz monomial
-- statement:
--   The leading Term Lemmas construction uses the map frz monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1741-L1743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1741-L1743

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K

theorem Formalism.GM.leadingTermLemmas.map_frz_monomial {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ) (m : Fin N × Fin r →₀ ℕ) :
    map ι (frz ℚ LL ρ n (monomial m 1)) = frz K LL ρ n (monomial m 1) := by sorry
