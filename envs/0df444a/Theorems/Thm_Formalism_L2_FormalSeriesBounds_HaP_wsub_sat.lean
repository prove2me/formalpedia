-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_wsub_sat
-- name    : Formalism.L2.FormalSeriesBounds.HaP.wsub_sat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:32.174349+00:00
-- url     : https://prove2.me/theorems/1a67dfdb-07e2-4f56-8660-6ffb96e4bfcc
-- title:
--   Ha P: wsub sat
-- statement:
--   The Ha P construction uses the wsub sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L221-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L221-L233

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)

theorem Formalism.L2.FormalSeriesBounds.HaP.wsub_sat (Bd : Finset (Letter Ty r n →₀ ℕ)) (z : ℤ) (x : Bd → ℤ) (hz : z ≠ 0)
    (hx : z • x ∈ Wsub r n cc isX a Bd) : x ∈ Wsub r n cc isX a Bd := by sorry
