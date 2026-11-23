-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_equiv
-- name    : Formalism.LogVandermondeBounds.product_first_zeroth_parts.exists_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:23.378459+00:00
-- url     : https://prove2.me/theorems/551b41df-a7ed-4b6e-8f62-6076c0f24eb2
-- title:
--   product first zeroth parts: exists equiv
-- statement:
--   The product first zeroth parts construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L165-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean#L165-L202

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset

theorem Formalism.LogVandermondeBounds.product_first_zeroth_parts.exists_equiv (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by sorry
