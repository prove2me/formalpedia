-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_natAbs_discr_eq
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.natAbs_discr_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:01.145087+00:00
-- url     : https://prove2.me/theorems/6647be92-5c60-4fc4-a334-ca90a79a9fd1
-- title:
--   B5: nat Abs discr eq
-- statement:
--   The B5 construction uses the nat Abs discr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/AbsNormInvMulDifferent.lean#L35-L43

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_AbsNormInvMulDifferent
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.natAbs_discr_eq (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
    [Algebra K E] (d : ℕ) (hdK : NumberField.discr K = -(d : ℤ)) :
    (NumberField.discr E).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) * d ^ Module.finrank K E := by sorry
