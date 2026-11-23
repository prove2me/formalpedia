-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_sum_single_ew
-- name    : Formalism.GM.leadingTermLemmas.sum_single_ew
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:42.112981+00:00
-- url     : https://prove2.me/theorems/ef788f13-3095-412e-87b3-2bf791d40b04
-- title:
--   leading Term Lemmas: sum single ew
-- statement:
--   The leading Term Lemmas construction uses the sum single ew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L197-L198

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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
variable (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem Formalism.GM.leadingTermLemmas.sum_single_ew (c : Fin r) : (∑ c', (Finsupp.single (e c) 1 : σ →₀ ℕ) (w c')) = 0 := by sorry
