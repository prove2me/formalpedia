-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_Xpow
-- name    : Formalism.GM.leadingTermLemmas.fk_Xpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:34.562009+00:00
-- url     : https://prove2.me/theorems/a0b5665c-5317-455e-a1bc-81783b262958
-- title:
--   leading Term Lemmas: fk Xpow
-- statement:
--   The leading Term Lemmas construction uses the fk Xpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1039-L1055
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1039-L1055

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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.leadingTermLemmas.fk_Xpow (i : σ) (k : ℕ) (g g' : MvPolynomial σ K) :
    fk (X i ^ k * g) (X i ^ k * g') =
      ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (((M i + k).descFactorial k : ℕ) : K) := by sorry
