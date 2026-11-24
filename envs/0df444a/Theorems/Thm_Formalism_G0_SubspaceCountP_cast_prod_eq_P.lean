-- Prove2me | Theorems.Thm_Formalism_G0_SubspaceCountP_cast_prod_eq_P
-- name    : Formalism.G0.SubspaceCountP.cast_prod_eq_P
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:08.496821+00:00
-- url     : https://prove2.me/theorems/042ed17a-0be7-46b2-9e3c-1a9344d3ae6f
-- title:
--   Subspace Count P: cast prod eq P
-- statement:
--   The Subspace Count P construction uses the cast prod eq P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/SubspaceCount.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/SubspaceCount.lean#L122-L128

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
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
open Module
open Formalism Formalism.G0
open Formalism.G0.SubspaceCountP
variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem Formalism.G0.SubspaceCountP.cast_prod_eq_P (q m k : ℕ) (hq : 1 ≤ q) (hm : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ i.val) : ℕ) : ℤ) = P (q : ℤ) m k := by sorry
