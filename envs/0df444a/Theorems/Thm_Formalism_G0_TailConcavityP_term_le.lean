-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_term_le
-- name    : Formalism.G0.TailConcavityP.term_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:54.969903+00:00
-- url     : https://prove2.me/theorems/4a2caa43-9dfe-4657-930e-3fcf9715cf40
-- title:
--   Tail Concavity P: term le
-- statement:
--   The Tail Concavity P construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L42-L52

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

theorem Formalism.G0.TailConcavityP.term_le (a b i : ℕ) :
    Real.log ((a : ℝ) + i + 1) - Real.log ((b : ℝ) + i + 1) ≤
      1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by sorry
