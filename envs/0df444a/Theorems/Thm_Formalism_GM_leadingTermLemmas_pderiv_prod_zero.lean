-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_pderiv_prod_zero
-- name    : Formalism.GM.leadingTermLemmas.pderiv_prod_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:48.048393+00:00
-- url     : https://prove2.me/theorems/731c774c-680a-4d98-b1dd-d2fe3c703cf2
-- title:
--   leading Term Lemmas: pderiv prod zero
-- statement:
--   The leading Term Lemmas construction uses the pderiv prod zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L954-L962
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L954-L962

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

theorem Formalism.GM.leadingTermLemmas.pderiv_prod_zero {σ' ι : Type} [DecidableEq ι] (i : σ') (t : Finset ι) (g : ι → MvPolynomial σ' K)
    (k : ι → ℕ) (h : ∀ x ∈ t, k x = 0 ∨ pderiv i (g x) = 0) : pderiv i (∏ x ∈ t, g x ^ k x) = 0 := by sorry
