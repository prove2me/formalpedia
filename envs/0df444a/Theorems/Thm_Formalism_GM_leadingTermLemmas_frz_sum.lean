-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_frz_sum
-- name    : Formalism.GM.leadingTermLemmas.frz_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:14.279805+00:00
-- url     : https://prove2.me/theorems/a0918a49-6d4d-4ee4-8bfd-d829cc953b9f
-- title:
--   leading Term Lemmas: frz sum
-- statement:
--   The leading Term Lemmas construction uses the frz sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1813-L1816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1813-L1816

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
variable {K : Type} [Field K]

theorem Formalism.GM.leadingTermLemmas.frz_sum {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) K) :
    frz K LL ρ n f = ∑ m ∈ f.support, f.coeff m • frz K LL ρ n (monomial m 1) := by sorry
