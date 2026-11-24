-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_as_sum_smul
-- name    : Formalism.GM.leadingTermLemmas.as_sum_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:27.823808+00:00
-- url     : https://prove2.me/theorems/70e857cb-9fd4-4835-9c80-4b48d19c6389
-- title:
--   leading Term Lemmas: as sum smul
-- statement:
--   The leading Term Lemmas construction uses the as sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1807-L1811
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1807-L1811

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
variable {K : Type} [Field K]

theorem Formalism.GM.leadingTermLemmas.as_sum_smul {σ : Type} (f : MvPolynomial σ K) :
    f = ∑ m ∈ f.support, f.coeff m • monomial m (1 : K) := by sorry
