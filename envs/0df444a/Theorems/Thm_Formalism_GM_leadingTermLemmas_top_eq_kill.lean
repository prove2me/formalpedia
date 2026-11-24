-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_top_eq_kill
-- name    : Formalism.GM.leadingTermLemmas.top_eq_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:29.217922+00:00
-- url     : https://prove2.me/theorems/79435537-2e6a-49ac-bd0a-fd7945d74360
-- title:
--   leading Term Lemmas: top eq kill
-- statement:
--   The leading Term Lemmas construction uses the top eq kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1151-L1178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1151-L1178

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

theorem Formalism.GM.leadingTermLemmas.top_eq_kill (a d : ℕ) (g g' : MvPolynomial (Fin (N + 1 + 1) × Fin r) K)
    (hg : BiHom (wW (N := N)) eη a d g) :
    ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M (Fin.last (N + 1), ρ) = d then 1 else 0) =
      fk (kill (Pη ρ) g) (kill (Pη ρ) g') := by sorry
