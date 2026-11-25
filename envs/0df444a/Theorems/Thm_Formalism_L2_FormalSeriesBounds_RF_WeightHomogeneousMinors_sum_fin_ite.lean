-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_sum_fin_ite
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.sum_fin_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:53:18.36684+00:00
-- url     : https://prove2.me/theorems/3a7f6b3f-151d-41f7-84e6-1c34e6fb004d
-- title:
--   Weight Homogeneous Minors: sum fin ite
-- statement:
--   The Weight Homogeneous Minors construction uses the sum fin ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L59-L69

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {R : Type} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.sum_fin_ite (k c0 : ℕ) : (∑ c : Fin k, if (c : ℕ) = c0 then 1 else 0) = if c0 < k then 1 else 0 := by sorry
