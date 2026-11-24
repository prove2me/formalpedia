-- Prove2me | Theorems.Thm_Formalism_GM_MeanGammaLemmas_poly_eq_of_eval
-- name    : Formalism.GM.MeanGammaLemmas.poly_eq_of_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:39.13581+00:00
-- url     : https://prove2.me/theorems/70759716-97ba-450f-96fb-822f2e238c4a
-- title:
--   Mean Gamma Lemmas: poly eq of eval
-- statement:
--   The Mean Gamma Lemmas construction uses the poly eq of eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L322-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean#L322-L331

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

theorem Formalism.GM.MeanGammaLemmas.poly_eq_of_eval (p : ℕ) [Fact p.Prime] (Q P : ℚ_[p][X]) (S : ℕ) (a : ℚ_[p])
    (h : ∀ n : ℕ, S ≤ n → Q.eval (n : ℚ_[p]) = a * P.eval (n : ℚ_[p])) : Q = C a * P := by sorry
