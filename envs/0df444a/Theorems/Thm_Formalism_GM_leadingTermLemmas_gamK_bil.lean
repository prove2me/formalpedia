-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_gamK_bil
-- name    : Formalism.GM.leadingTermLemmas.gamK_bil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:21.355726+00:00
-- url     : https://prove2.me/theorems/94e182e0-1892-4f73-af13-7ae8102678cd
-- title:
--   leading Term Lemmas: gam K bil
-- statement:
--   The leading Term Lemmas construction uses the gam K bil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1818-L1826
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1818-L1826

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

theorem Formalism.GM.leadingTermLemmas.gamK_bil {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) K) :
    gamK K LL ρ z n f f' = ∑ m ∈ f.support, ∑ m' ∈ f'.support,
      f.coeff m * f'.coeff m' * gamK K LL ρ z n (monomial m 1) (monomial m' 1) := by sorry
