-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sq
-- name    : Formalism.GM.leadingTermLemmas.biHom_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:18.249823+00:00
-- url     : https://prove2.me/theorems/27de3673-f274-4e2b-9663-951360d4fa15
-- title:
--   leading Term Lemmas: bi Hom sq
-- statement:
--   The leading Term Lemmas construction uses the bi Hom sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L921-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L921-L924

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

theorem Formalism.GM.leadingTermLemmas.biHom_sq (m : Fin (N + 1) × Fin r →₀ ℕ) :
    BiHom (wW (N := N)) eη (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * (if x.1 = Fin.last N then 1 else 0))
      (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * 1) (sq (K := K) LL ρ m) := by sorry
