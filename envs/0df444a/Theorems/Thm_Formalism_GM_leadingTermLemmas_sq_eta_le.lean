-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_sq_eta_le
-- name    : Formalism.GM.leadingTermLemmas.sq_eta_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:19.757352+00:00
-- url     : https://prove2.me/theorems/2c7947a1-734d-40eb-9aef-4919260a7afc
-- title:
--   leading Term Lemmas: sq eta le
-- statement:
--   The leading Term Lemmas construction uses the sq eta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1422-L1428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1422-L1428

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
variable (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m)
  (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) (hn : LL.total ≤ n)
include hm hme hn
omit hn hme

theorem Formalism.GM.leadingTermLemmas.sq_eta_le (he : m (Fin.last N, ρ) = e) : ∀ M ∈ (sq (K := K) LL ρ m).support, M (Fin.last (N + 1), ρ) ≤ LL.total - e := by sorry
