-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_kill_sq
-- name    : Formalism.GM.leadingTermLemmas.fk_kill_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:05.462602+00:00
-- url     : https://prove2.me/theorems/42d2e4d7-5426-4190-aa5e-a8c1f5abc5d6
-- title:
--   leading Term Lemmas: fk kill sq
-- statement:
--   The leading Term Lemmas construction uses the fk kill sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1518-L1537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L1518-L1537

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem Formalism.GM.leadingTermLemmas.fk_kill_sq (m m' : Fin (N + 1) × Fin r →₀ ℕ) (d : ℕ)
    (hd : ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = d) (hd' : ∑ x, (Finsupp.update m' (Fin.last N, ρ) 0) x = d) :
    fk (kill (K := K) (Pη ρ) (sq LL ρ m)) (kill (Pη ρ) (sq LL ρ m')) =
      if Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0 then
        (d.factorial : K) * wf (Finsupp.update m (Fin.last N, ρ) 0) else 0 := by sorry
