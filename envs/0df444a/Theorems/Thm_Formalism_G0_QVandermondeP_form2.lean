-- Prove2me | Theorems.Thm_Formalism_G0_QVandermondeP_form2
-- name    : Formalism.G0.QVandermondeP.form2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:24.08247+00:00
-- url     : https://prove2.me/theorems/5de3ace2-dbe4-4066-a1fb-56a343e9cc61
-- title:
--   QVandermonde P: form2
-- statement:
--   The QVandermonde P construction uses the form2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L24-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/QVandermonde.lean#L24-L65

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

theorem Formalism.G0.QVandermondeP.form2 (q m : ℕ) : ∀ g n : ℕ, gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l := by sorry
