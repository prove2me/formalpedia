-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_smul
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Good.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:21.098851+00:00
-- url     : https://prove2.me/theorems/e2191519-72b8-4170-82c7-f05f66811fcc
-- title:
--   Good: smul
-- statement:
--   The Good construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L78-L79

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
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

theorem Formalism.MainNotions.PlaneGram.TwistData.Good.smul {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (a : K) :
    D.Good p (a • Z) := by sorry
