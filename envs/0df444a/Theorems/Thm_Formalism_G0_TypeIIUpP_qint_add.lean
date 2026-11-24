-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIUpP_qint_add
-- name    : Formalism.G0.TypeIIUpP.qint_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:13.72112+00:00
-- url     : https://prove2.me/theorems/640b53fa-095c-4888-971f-ce5aa224943a
-- title:
--   Type IIUp P: qint add
-- statement:
--   The Type IIUp P construction uses the qint add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIUp.lean#L30-L36

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

theorem Formalism.G0.TypeIIUpP.qint_add (q a b : ℕ) : qint q (a + b) = qint q a + q ^ a * qint q b := by sorry
