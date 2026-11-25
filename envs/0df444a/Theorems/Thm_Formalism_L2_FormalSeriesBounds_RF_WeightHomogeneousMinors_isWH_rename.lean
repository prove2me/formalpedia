-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_rename
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_rename
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:01.765495+00:00
-- url     : https://prove2.me/theorems/e4236c52-1452-4073-abce-0babdea5153c
-- title:
--   Weight Homogeneous Minors: is WH rename
-- statement:
--   The Weight Homogeneous Minors construction uses the is WH rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L18-L24

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

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_rename {σ τ : Type} {w : τ → ℕ} (f : σ → τ) {p : MvPolynomial σ R} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) p D) : IsWeightedHomogeneous w (rename f p) D := by sorry
