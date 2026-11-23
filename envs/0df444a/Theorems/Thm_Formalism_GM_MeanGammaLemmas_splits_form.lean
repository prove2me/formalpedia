-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_splits_form
-- name    : Formalism.GM.MeanGammaLemmas.splits_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:18.83379+00:00
-- url     : https://prove2.me/theorems/5312b2bc-34de-4236-b4b2-3ec0cd1e5076
-- title:
--   Mean Gamma Lemmas: splits form
-- statement:
--   The Mean Gamma Lemmas construction uses the splits form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L369-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L369-L372

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

theorem Formalism.GM.MeanGammaLemmas.splits_form {L : Type} [Field L] [IsAlgClosed L] (Dk : L[X]) :
    Dk = C Dk.leadingCoeff * (Dk.roots.map (fun ζ => X - C ζ)).prod ∧ Dk.roots.card = Dk.natDegree := by sorry
