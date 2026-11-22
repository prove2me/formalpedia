-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_eq_sum
-- name    : Formalism.GM.leadingTermLemmas.fk_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:28.375543+00:00
-- url     : https://prove2.me/theorems/77077bab-fd9a-417e-8a06-ec0dcbbc4525
-- title:
--   leading Term Lemmas: fk eq sum
-- statement:
--   The leading Term Lemmas construction uses the fk eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L31-L36

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

theorem Formalism.GM.leadingTermLemmas.fk_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (h : F.support ⊆ s) :
    fk F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by sorry
