-- Prove2me | Theorems.Thm_Formalism_G0_TailSumsP_clause1
-- name    : Formalism.G0.TailSumsP.clause1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:28.502526+00:00
-- url     : https://prove2.me/theorems/38fda06c-d828-49fe-812b-b68289777205
-- title:
--   Tail Sums P: clause1
-- statement:
--   The Tail Sums P construction uses the clause1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L83-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L83-L110

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

theorem Formalism.G0.TailSumsP.clause1 {K : ℕ} (steps : List (Option ℕ)) (what₂ : ℕ → Fin K → ℕ)
    (hp : IsPath steps what₂) :
    ∀ i ≤ steps.length, ∀ u, tailK (what₂ i) u ≤ ((latestDegrees steps i).drop u).sum := by sorry
