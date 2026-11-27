-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_eq_zero_of_ge_all
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.eq_zero_of_ge_all
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:07:41.118117+00:00
-- url     : https://prove2.me/theorems/afad7ef8-d410-46c3-80b2-190b7240f1d5
-- title:
--   Gm Ex Arith: eq zero of ge all
-- statement:
--   The Gm Ex Arith construction uses the eq zero of ge all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L82-L90

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.GmExArith.eq_zero_of_ge_all {x : C} (h : ∀ n : ℕ, V.Ge n x) : x = 0 := by sorry
