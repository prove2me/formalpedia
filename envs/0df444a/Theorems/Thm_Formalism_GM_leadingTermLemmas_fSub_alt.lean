-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fSub_alt
-- name    : Formalism.GM.leadingTermLemmas.fSub_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:41.788133+00:00
-- url     : https://prove2.me/theorems/6f327237-abb7-4b26-a557-94bb514107ae
-- title:
--   leading Term Lemmas: f Sub alt
-- statement:
--   The leading Term Lemmas construction uses the f Sub alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L882-L884
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L882-L884

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.fSub_alt (hv : LL.vec (Fin.last N) = true) :
    fSub K LL ρ (Fin.last N, ρ) = ∑ c, X (wW (N := N) c) * X (eη c) := by sorry
