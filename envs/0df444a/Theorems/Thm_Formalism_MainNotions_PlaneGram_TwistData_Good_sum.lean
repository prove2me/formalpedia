-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_sum
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Good.sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:52.520411+00:00
-- url     : https://prove2.me/theorems/937ea145-bf3a-4a92-8f7a-2ca29c88438a
-- title:
--   Good: sum
-- statement:
--   The Good construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/Monomial.lean#L84-L91

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

theorem Formalism.MainNotions.PlaneGram.TwistData.Good.sum {p : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (D.ML × Fin D.r) K)
    (h : ∀ i ∈ s, D.Good p (f i)) : D.Good p (∑ i ∈ s, f i) := by sorry
