-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_aeval_fSub_monomial
-- name    : Formalism.GM.leadingTermLemmas.aeval_fSub_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:20.569078+00:00
-- url     : https://prove2.me/theorems/77d6d6b4-93cb-4b56-b370-db51bfbdbc11
-- title:
--   leading Term Lemmas: aeval f Sub monomial
-- statement:
--   The leading Term Lemmas construction uses the aeval f Sub monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L866-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L866-L869

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

theorem Formalism.GM.leadingTermLemmas.aeval_fSub_monomial (m : Fin (N + 1) × Fin r →₀ ℕ) :
    aeval (fSub K LL ρ) (monomial m (1 : K)) = ∏ x, fSub K LL ρ x ^ m x := by sorry
