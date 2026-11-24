-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_sum_trunc
-- name    : Formalism.GM.MeanGammaLemmas.sum_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:48.073508+00:00
-- url     : https://prove2.me/theorems/2241dd97-f8ce-4e2b-a050-447578cec9f3
-- title:
--   Mean Gamma Lemmas: sum trunc
-- statement:
--   The Mean Gamma Lemmas construction uses the sum trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L314-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L314-L320

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M

theorem Formalism.GM.MeanGammaLemmas.sum_trunc {F : Type} [Field F] (D0 del : ℕ) (h : D0 ≤ del) (g : ℕ → F) :
    ∑ k ∈ range (del + 1), (if k ≤ D0 then g k else 0) = ∑ k ∈ range (D0 + 1), g k := by sorry
