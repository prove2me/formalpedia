-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_isWH_add
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:16:44.299066+00:00
-- url     : https://prove2.me/theorems/767a2bd9-bfeb-4431-bc80-77969e1e9ed7
-- title:
--   Weight Homogeneous Letters: is WH add
-- statement:
--   The Weight Homogeneous Letters construction uses the is WH add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IsWHLetterMinorK.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IsWHLetterMinorK.lean#L36-L44

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
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
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
open WeightHomogeneousMinors
variable {R : Type} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_add {σ : Type} {w1 w2 : σ → ℕ} {p : MvPolynomial σ R} {D1 D2 : ℕ}
    (h1 : IsWeightedHomogeneous w1 p D1) (h2 : IsWeightedHomogeneous w2 p D2) :
    IsWeightedHomogeneous (fun x => w1 x + w2 x) p (D1 + D2) := by sorry
