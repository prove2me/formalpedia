-- Prove2me | Theorems.Thm_Formalism_L2_Col_XgE_irr
-- name    : Formalism.L2.Col.XgE_irr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:01.082959+00:00
-- url     : https://prove2.me/theorems/bf0b0002-6179-4240-a283-39a1001b04d9
-- title:
--   Col: Xg E irr
-- statement:
--   The Col construction uses the Xg E irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgE.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgE.lean#L26-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.L2.DIV
variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Col.XgE_irr {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} : ∀ χ ∈ XgE σ e, IsAbsIrrChar χ := by sorry
