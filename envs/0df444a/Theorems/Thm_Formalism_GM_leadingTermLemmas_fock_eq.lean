-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fock_eq
-- name    : Formalism.GM.leadingTermLemmas.fock_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:40.857986+00:00
-- url     : https://prove2.me/theorems/aefc198b-9463-45c1-9c24-7854e78a0aff
-- title:
--   leading Term Lemmas: fock eq
-- statement:
--   The leading Term Lemmas construction uses the fock eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L754-L756
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L754-L756

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

theorem Formalism.GM.leadingTermLemmas.fock_eq (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p F G = fk F G := by sorry
