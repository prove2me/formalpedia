-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_limit_value
-- name    : Formalism.GM.leadingTermLemmas.limit_value
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:20.24565+00:00
-- url     : https://prove2.me/theorems/59271e43-7a9e-4bcb-bfe3-2fd0b27e7523
-- title:
--   leading Term Lemmas: limit value
-- statement:
--   The leading Term Lemmas construction uses the limit value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1557-L1599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1557-L1599

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
open MvPolynomial Finset Formalism.GM Filter Topology
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.limit_value (z e : ℕ) (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m') :
    (1 / ((LL.deg (Fin.last N)).factorial : ℝ)) *
      (((z + e).choose e : ℝ) * e.factorial * e.factorial *
        (if m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e then
          ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
            (if M (Fin.last (N + 1), ρ) = LL.total - e then 1 / ((LL.total - e).factorial : ℝ) else 0)
        else 0) + 0) /
      (((LL.total).factorial : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) =
    (((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
      ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) := by sorry
