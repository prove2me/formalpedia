-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sum_right
-- name    : Formalism.GM.leadingTermLemmas.fk_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:18.817592+00:00
-- url     : https://prove2.me/theorems/71f98d8f-c1cf-42ee-8e70-a85f23ecd0ef
-- title:
--   leading Term Lemmas: fk sum right
-- statement:
--   The leading Term Lemmas construction uses the fk sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L87-L89

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
open MvPolynomial Finset
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.leadingTermLemmas.fk_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ K) (G : ι → MvPolynomial σ K) :
    fk F (∑ i ∈ t, G i) = ∑ i ∈ t, fk F (G i) := by sorry
