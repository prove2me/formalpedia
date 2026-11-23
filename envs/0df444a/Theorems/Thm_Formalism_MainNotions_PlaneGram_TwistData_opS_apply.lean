-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_opS_apply
-- name    : Formalism.MainNotions.PlaneGram.TwistData.opS_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:43.245437+00:00
-- url     : https://prove2.me/theorems/4a13780d-e865-4329-b93d-d716470d5983
-- title:
--   Twist Data: op S apply
-- statement:
--   The Twist Data construction uses the op S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L472-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L472-L474

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)

theorem Formalism.MainNotions.PlaneGram.TwistData.opS_apply (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) (Q : MvPolynomial (D.ML × Fin D.r) K) :
    D.opS t μ κ1 c1 Q = c1 • (monomial (onLetter (D.mw t) μ) (1 : K) * ddiv (onLetter (D.mw t) κ1) Q) := by sorry
