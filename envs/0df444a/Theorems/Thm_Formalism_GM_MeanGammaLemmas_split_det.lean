-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_split_det
-- name    : Formalism.GM.MeanGammaLemmas.split_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:54.076806+00:00
-- url     : https://prove2.me/theorems/af71f8a8-3bf4-4ec2-93f1-aec2c0b678ed
-- title:
--   Mean Gamma Lemmas: split det
-- statement:
--   The Mean Gamma Lemmas construction uses the split det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L363-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L363-L367

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

theorem Formalism.GM.MeanGammaLemmas.split_det (p : ℕ) [Fact p.Prime] {n : ℕ} (Aq : Matrix (Fin n) (Fin n) ℚ_[p][X]) :
    (Aq.map (Polynomial.map (algebraMap ℚ_[p] (PadicAlgCl p)))).det =
      (Aq.det).map (algebraMap ℚ_[p] (PadicAlgCl p)) := by sorry
