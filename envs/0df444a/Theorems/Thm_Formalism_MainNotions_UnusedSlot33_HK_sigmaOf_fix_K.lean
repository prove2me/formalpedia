-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_sigmaOf_fix_K
-- name    : Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:34.088563+00:00
-- url     : https://prove2.me/theorems/7727455c-73d9-4d94-84d9-e8f26115aab9
-- title:
--   HK: sigma Of fix K
-- statement:
--   The HK construction uses the sigma Of fix K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L48-L54

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

theorem Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K (g : R.GG) (hg : g ∈ R.Psi) (x : H.E) (hx : x ∈ H.K) :
    H.sigmaOf g x = x := by sorry
