-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_freeze_eq
-- name    : Formalism.GM.leadingTermLemmas.freeze_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:54.293841+00:00
-- url     : https://prove2.me/theorems/64b6f72f-5c23-480d-82aa-da3552aba92f
-- title:
--   leading Term Lemmas: freeze eq
-- statement:
--   The leading Term Lemmas construction uses the freeze eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L758-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L758-L759

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

theorem Formalism.GM.leadingTermLemmas.freeze_eq (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.freeze p LL ρ n f = frz ℚ_[p] LL ρ n f := by sorry
