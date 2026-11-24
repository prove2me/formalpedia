-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_kill_sq
-- name    : Formalism.GM.leadingTermLemmas.kill_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:19.178795+00:00
-- url     : https://prove2.me/theorems/d7565bf6-b516-45eb-b3d3-db2506d4f16d
-- title:
--   leading Term Lemmas: kill sq
-- statement:
--   The leading Term Lemmas construction uses the kill sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1128-L1136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1128-L1136

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

theorem Formalism.GM.leadingTermLemmas.kill_sq (m : Fin (N + 1) × Fin r →₀ ℕ) :
    kill (K := K) (Pη ρ) (sq LL ρ m) =
      X (Fin.last (N + 1), ρ) ^ (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x) *
        monomial ((Finsupp.update m (Fin.last N, ρ) 0).mapDomain cs') 1 := by sorry
