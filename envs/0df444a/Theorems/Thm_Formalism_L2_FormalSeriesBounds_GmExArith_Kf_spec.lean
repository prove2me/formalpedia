-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_Kf_spec
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.Kf_spec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:43.3283+00:00
-- url     : https://prove2.me/theorems/4fa16108-00dc-57c6-bb64-15dda83a620e
-- title:
--   Gm Ex Arith: Kf spec
-- statement:
--   The Gm Ex Arith construction uses the Kf spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L208-L211

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.Kf_spec {ε : ℝ} (hε : 0 < ε) (n : ℕ) : (n : ℝ) ≤ (Kf ε n : ℝ) * ε := by sorry
