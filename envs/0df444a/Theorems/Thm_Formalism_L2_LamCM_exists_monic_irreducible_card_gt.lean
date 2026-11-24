-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_exists_monic_irreducible_card_gt
-- name    : Formalism.L2.LamCM.exists_monic_irreducible_card_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:05.888891+00:00
-- url     : https://prove2.me/theorems/96a299d6-ad36-4f6a-843b-eeb8d48c29e1
-- title:
--   Lam CM: exists monic irreducible card gt
-- statement:
--   The Lam CM construction uses the exists monic irreducible card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsMonicIrreducibleCardGt.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsMonicIrreducibleCardGt.lean#L9-L43

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open Polynomial IsLocalRing

theorem Formalism.L2.LamCM.exists_monic_irreducible_card_gt (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ N < Nat.card (AdjoinRoot f) := by sorry
