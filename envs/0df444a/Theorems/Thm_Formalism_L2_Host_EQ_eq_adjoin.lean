-- Prove2me | Theorems.Thm_Formalism_L2_Host_EQ_eq_adjoin
-- name    : Formalism.L2.Host.EQ_eq_adjoin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:32.92781+00:00
-- url     : https://prove2.me/theorems/e4d1e132-5b1d-41a2-8472-fe519828cee5
-- title:
--   Host: EQ eq adjoin
-- statement:
--   The Host construction uses the EQ eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean#L73-L77

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.L2.Host.EQ_eq_adjoin (e q d : ℕ) : EQ e q d =
    adjoin ℚ ((sqrts (-(q : ℤ)) ∪ sqrts (-(d : ℤ))) ∪ (fun z => z + z⁻¹) '' mus (2 ^ (e + 2))) := by sorry
