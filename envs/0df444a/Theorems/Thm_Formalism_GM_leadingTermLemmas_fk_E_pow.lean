-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_E_pow
-- name    : Formalism.GM.leadingTermLemmas.fk_E_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:32.55591+00:00
-- url     : https://prove2.me/theorems/69236db3-dc3c-44f9-ba82-ef6f858c6802
-- title:
--   leading Term Lemmas: fk E pow
-- statement:
--   The leading Term Lemmas construction uses the fk E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L114-L119

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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.leadingTermLemmas.fk_E_pow (j : ℕ) (g h : MvPolynomial σ K) :
    fk ((Formalism.GM.tieE w e ^ j) g) h = fk g ((Formalism.GM.tieF w e ^ j) h) := by sorry
