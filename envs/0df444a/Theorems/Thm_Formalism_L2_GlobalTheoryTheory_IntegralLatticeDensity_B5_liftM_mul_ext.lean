-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_mul_ext
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.liftM_mul_ext
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:50:16.325214+00:00
-- url     : https://prove2.me/theorems/2682e8bd-34fb-4fc2-b6c9-9789fa17e9c0
-- title:
--   B5: lift M mul ext
-- statement:
--   The B5 construction uses the lift M mul ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/LiftMOneExt.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/LiftMOneExt.lean#L13-L17

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.liftM_mul_ext {E : Type} [Field E] (M : IntermediateField ℚ ℂ) (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M)
    (a b : E) : liftM M (σ (a * b)) = liftM M (σ a) * liftM M (σ b) := by sorry
