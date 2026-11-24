-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_la_core
-- name    : Formalism.CohomologicalDescent.LA.la_core
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:16.82669+00:00
-- url     : https://prove2.me/theorems/4df54377-62ec-49c1-98e7-7bf7873bebfe
-- title:
--   LA: la core
-- statement:
--   The LA construction uses the la core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L405-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ProdInitialMinorsMemDetSpan.lean#L405-L432

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LA.la_core {n : ℕ} (s : Fin n) (d : ℕ) (g : MvPolynomial (Fin 2 × Fin n) ℤ) (hg : g ≠ 0)
    (l e : ℕ) (hl : l.Prime) :
    (∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ (la_monLat ℤ s d).map (LinearMap.mulLeft ℤ g),
      ((m * l ^ e : ℕ) : ℤ) • x ∈ (la_binLat ℤ s d).map (LinearMap.mulLeft ℤ g)) ↔
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by sorry
