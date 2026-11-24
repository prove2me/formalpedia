-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_tele
-- name    : Formalism.G0.TailConcavityP.tele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:29.153814+00:00
-- url     : https://prove2.me/theorems/c1a03026-07d1-4369-99aa-da36ebc8185b
-- title:
--   Tail Concavity P: tele
-- statement:
--   The Tail Concavity P construction uses the tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L105-L111

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP

theorem Formalism.G0.TailConcavityP.tele (k N : ℕ) (B : Fin N → ℕ) (l : ℕ) :
    ∑ u ∈ range (l + 1), en k N B u = cn k N B l := by sorry
