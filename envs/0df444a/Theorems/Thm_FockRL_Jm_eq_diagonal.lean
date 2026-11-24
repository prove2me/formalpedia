-- Prove2me | Theorems.Thm_FockRL_Jm_eq_diagonal
-- name    : FockRL.Jm_eq_diagonal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:25.451802+00:00
-- url     : https://prove2.me/theorems/45cd238c-cb13-4c93-9e84-318a23c2d1d3
-- title:
--   Fock RL: Jm eq diagonal
-- statement:
--   The Fock RL construction uses the Jm eq diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open FockRL

theorem FockRL.Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by sorry
