-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_prod_split
-- name    : Formalism.GM.leadingTermLemmas.prod_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:55.988805+00:00
-- url     : https://prove2.me/theorems/e1313793-0508-4661-a08d-9ff95e4a3d01
-- title:
--   leading Term Lemmas: prod split
-- statement:
--   The leading Term Lemmas construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L871-L880
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L871-L880

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

theorem Formalism.GM.leadingTermLemmas.prod_split {σ' : Type} [Fintype σ'] [DecidableEq σ'] {R : Type} [CommMonoid R] (g : σ' → R)
    (m : σ' →₀ ℕ) (x0 : σ') :
    ∏ x, g x ^ m x = g x0 ^ m x0 * ∏ x, g x ^ (Finsupp.update m x0 0) x := by sorry
