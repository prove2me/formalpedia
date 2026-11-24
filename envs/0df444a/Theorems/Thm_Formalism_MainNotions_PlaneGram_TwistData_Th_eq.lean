-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_eq
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Th_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:04:04.784126+00:00
-- url     : https://prove2.me/theorems/3e265f38-a3a8-404f-a7e1-d2003c6813af
-- title:
--   Twist Data: Th eq
-- statement:
--   The Twist Data construction uses the Th eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L43-L65

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem Formalism.MainNotions.PlaneGram.TwistData.Th_eq (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.Th j cc PP Z = ∑ μ ∈ Z.support.image (eOut (D.outSeg j)),
      monomial μ 1 * D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) := by sorry
