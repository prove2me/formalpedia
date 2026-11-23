-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_E_pow_X_mul
-- name    : Formalism.GM.leadingTermLemmas.E_pow_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:18.854776+00:00
-- url     : https://prove2.me/theorems/2750df24-7ab6-4571-b858-8c815c23e265
-- title:
--   leading Term Lemmas: E pow X mul
-- statement:
--   The leading Term Lemmas construction uses the E pow X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1319-L1322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1319-L1322

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)

theorem Formalism.GM.leadingTermLemmas.E_pow_X_mul (j k : ℕ) (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) :
    (tieE (wW (N := N)) eη ^ j) (X (Fin.last (N + 1), ρ) ^ k * g) =
      X (Fin.last (N + 1), ρ) ^ k * (tieE (wW (N := N)) eη ^ j) g := by sorry
