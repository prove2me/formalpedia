-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_gb_symm
-- name    : Formalism.G0.TypeIIUpP.gb_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:34.760124+00:00
-- url     : https://prove2.me/theorems/27f10570-ba17-4e43-aeff-a59bd1a75921
-- title:
--   Type IIUp P: gb symm
-- statement:
--   The Type IIUp P construction uses the gb symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L73-L80

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
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
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP

theorem Formalism.G0.TypeIIUpP.gb_symm (q n k : ℕ) (h : k ≤ n) : gaussBinom q n k = gaussBinom q n (n - k) := by sorry
