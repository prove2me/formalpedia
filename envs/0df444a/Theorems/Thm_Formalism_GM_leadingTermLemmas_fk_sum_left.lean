-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sum_left
-- name    : Formalism.GM.leadingTermLemmas.fk_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:57.334923+00:00
-- url     : https://prove2.me/theorems/cf5e5a3d-0295-4431-84e2-6c17969af73a
-- title:
--   leading Term Lemmas: fk sum left
-- statement:
--   The leading Term Lemmas construction uses the fk sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L69-L74

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

theorem Formalism.GM.leadingTermLemmas.fk_sum_left {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fk (∑ i ∈ t, F i) G = ∑ i ∈ t, fk (F i) G := by sorry
