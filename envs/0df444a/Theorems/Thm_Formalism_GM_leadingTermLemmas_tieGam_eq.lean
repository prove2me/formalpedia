-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_tieGam_eq
-- name    : Formalism.GM.leadingTermLemmas.tieGam_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:07.839801+00:00
-- url     : https://prove2.me/theorems/c01c66d5-33ab-4e47-9d41-22a3417fcccc
-- title:
--   leading Term Lemmas: tie Gam eq
-- statement:
--   The leading Term Lemmas construction uses the tie Gam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L761-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L761-L766

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

theorem Formalism.GM.leadingTermLemmas.tieGam_eq (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.tieGam p LL ρ z n f f' = gamK ℚ_[p] LL ρ z n f f' := by sorry
