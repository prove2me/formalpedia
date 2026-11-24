-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_eq_of_le_of_absNorm_eq
-- name    : Formalism.MainNotions.UnusedSlot33.HK.eq_of_le_of_absNorm_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:35.181018+00:00
-- url     : https://prove2.me/theorems/e34731b3-9985-48d6-b644-bc6c7fc403e5
-- title:
--   HK: eq of le of abs Norm eq
-- statement:
--   The HK construction uses the eq of le of abs Norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L91-L99

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)

theorem Formalism.MainNotions.UnusedSlot33.HK.eq_of_le_of_absNorm_eq {K : Type*} [Field K] [NumberField K] {I J : Ideal (𝓞 K)}
    (hle : I ≤ J) (hI : Ideal.absNorm I ≠ 0) (h : Ideal.absNorm I = Ideal.absNorm J) : I = J := by sorry
