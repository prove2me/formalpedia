-- Prove2me | Theorems.Thm_Formalism_L2_Col_mem_XgE
-- name    : Formalism.L2.Col.mem_XgE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:16.304805+00:00
-- url     : https://prove2.me/theorems/3b6d66be-45a6-4501-9a9c-ecdc7d475e6a
-- title:
--   Col: mem Xg E
-- statement:
--   The Col construction uses the mem Xg E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgE.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgE.lean#L22-L24

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

theorem Formalism.L2.Col.mem_XgE {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} {χ : G → K} :
    χ ∈ XgE σ e ↔ IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1) := by sorry
