-- Prove2me | Theorems.Thm_Formalism_G0_QVandermondeP_form1
-- name    : Formalism.G0.QVandermondeP.form1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:35.849795+00:00
-- url     : https://prove2.me/theorems/543cfb72-f6a3-4d6e-ae15-db1944c9d1ac
-- title:
--   QVandermonde P: form1
-- statement:
--   The QVandermonde P construction uses the form1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L67-L81

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.QVandermondeP

theorem Formalism.G0.QVandermondeP.form1 (q m g n : ℕ) : gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l := by sorry
