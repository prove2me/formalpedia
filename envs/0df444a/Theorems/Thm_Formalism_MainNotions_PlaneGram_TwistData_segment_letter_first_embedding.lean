-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_segment_letter_first_embedding
-- name    : Formalism.MainNotions.PlaneGram.TwistData.segment_letter_first_embedding
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:05:52.062424+00:00
-- url     : https://prove2.me/theorems/542ec916-1911-443c-ac52-128c411c5d32
-- title:
--   Twist Data: segment letter first embedding
-- statement:
--   The Twist Data construction uses the segment letter first embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L119-L122

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
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

theorem Formalism.MainNotions.PlaneGram.TwistData.segment_letter_first_embedding (k : Fin (D.nB j + D.r)) : D.SegL j (D.e0 j k) := by sorry
