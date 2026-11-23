-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_support_X_mul
-- name    : Formalism.GM.leadingTermLemmas.support_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:59.213395+00:00
-- url     : https://prove2.me/theorems/d646efe8-1c8d-4c7b-8566-c409d0c06ba1
-- title:
--   leading Term Lemmas: support X mul
-- statement:
--   The leading Term Lemmas construction uses the support X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L181-L183

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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem Formalism.GM.leadingTermLemmas.support_X_mul (i : σ) (g : MvPolynomial σ K) :
    (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by sorry
