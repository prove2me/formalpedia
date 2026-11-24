-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_fSub
-- name    : Formalism.GM.leadingTermLemmas.biHom_fSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:16.188808+00:00
-- url     : https://prove2.me/theorems/eb9d369d-9faf-4c8f-8eb7-183c117152ee
-- title:
--   leading Term Lemmas: bi Hom f Sub
-- statement:
--   The leading Term Lemmas construction uses the bi Hom f Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L848-L864
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L848-L864

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

theorem Formalism.GM.leadingTermLemmas.biHom_fSub (x : Fin (N + 1) × Fin r) :
    BiHom (wW (N := N)) eη (if x.1 = Fin.last N then 1 else 0) 1 (fSub K LL ρ x) := by sorry
