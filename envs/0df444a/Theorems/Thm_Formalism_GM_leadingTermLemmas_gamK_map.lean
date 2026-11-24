-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_gamK_map
-- name    : Formalism.GM.leadingTermLemmas.gamK_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:17.943907+00:00
-- url     : https://prove2.me/theorems/a41d7d62-b210-4c1e-8d52-41c49be4edb4
-- title:
--   leading Term Lemmas: gam K map
-- statement:
--   The leading Term Lemmas construction uses the gam K map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1786-L1790
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1786-L1790

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
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.leadingTermLemmas.gamK_map {N : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ) (m m' : Fin (N + 1) × Fin r →₀ ℕ) :
    gamK K LL ρ z n (monomial m 1) (monomial m' 1) = ι (gamK ℚ LL ρ z n (monomial m 1) (monomial m' 1)) := by sorry
