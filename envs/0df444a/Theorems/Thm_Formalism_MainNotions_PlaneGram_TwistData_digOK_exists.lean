-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digOK_exists
-- name    : Formalism.MainNotions.PlaneGram.TwistData.digOK_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:04:02.649028+00:00
-- url     : https://prove2.me/theorems/c91d6458-a206-40c1-aa1a-63522e1739ae
-- title:
--   Twist Data: dig OK exists
-- statement:
--   The Twist Data construction uses the dig OK exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L235-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L235-L240

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.digOK_exists (hDIG : DIG K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c) :
    ∃ cst gam, D.DigOK v p cst gam := by sorry
