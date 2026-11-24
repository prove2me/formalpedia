-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_pderiv_W_fSub
-- name    : Formalism.GM.leadingTermLemmas.pderiv_W_fSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:06.269512+00:00
-- url     : https://prove2.me/theorems/6dbe28e1-69ae-438f-9e5f-e348ea6f92f3
-- title:
--   leading Term Lemmas: pderiv W f Sub
-- statement:
--   The leading Term Lemmas construction uses the pderiv W f Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L964-L988
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L964-L988

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.pderiv_W_fSub (hv : LL.vec (Fin.last N) = true) (x : Fin (N + 1) × Fin r) (hx : x ≠ (Fin.last N, ρ)) :
    pderiv (wW (N := N) ρ) (fSub K LL ρ x) = 0 := by sorry
