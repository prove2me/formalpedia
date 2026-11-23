-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_eIn
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:41.314124+00:00
-- url     : https://prove2.me/theorems/2a100ff7-50b8-46fe-8581-0a4660512f0e
-- title:
--   Twist Data: ldeg e In
-- statement:
--   The Twist Data construction uses the ldeg e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L50-L55

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

theorem Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn (ζ : D.EM) (i : D.ML) : ldeg (eIn D.outP ζ) i = if D.outP i then 0 else ldeg ζ i := by sorry
