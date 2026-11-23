-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_tieE_pow_eq
-- name    : Formalism.GM.leadingTermLemmas.tieE_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:25.13371+00:00
-- url     : https://prove2.me/theorems/0e54dc37-da22-4de7-9de1-9bedb7938e84
-- title:
--   leading Term Lemmas: tie E pow eq
-- statement:
--   The leading Term Lemmas construction uses the tie E pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L886-L890
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L886-L890

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

theorem Formalism.GM.leadingTermLemmas.tieE_pow_eq (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) (a : ℕ) :
    (tieE (wW (N := N)) eη ^ a) g = (∑ c, X (wW (N := N) c) * X (eη c)) ^ a * g := by sorry
