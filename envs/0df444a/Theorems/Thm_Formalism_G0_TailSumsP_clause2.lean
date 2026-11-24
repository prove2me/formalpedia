-- Prove2me | Theorems.Thm_Formalism_G0_TailSumsP_clause2
-- name    : Formalism.G0.TailSumsP.clause2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:43.872656+00:00
-- url     : https://prove2.me/theorems/6b80c379-7ee7-4091-b555-3fd08ca81f8b
-- title:
--   Tail Sums P: clause2
-- statement:
--   The Tail Sums P construction uses the clause2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L112-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L112-L138

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP

theorem Formalism.G0.TailSumsP.clause2 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) (i u X : ℕ)
    (hX : tailK (what₂ i) u + X ≤ ((latestDegrees steps i).drop u).sum) :
    ∀ j, i ≤ j → j ≤ steps.length →
      tailK (what₂ j) (u + cnt steps i j) + X ≤
        ((latestDegrees steps j).drop (u + cnt steps i j)).sum := by sorry
