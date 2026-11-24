-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_gen_top
-- name    : Formalism.MainNotions.UnusedSlot33.HK.gen_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:59.291819+00:00
-- url     : https://prove2.me/theorems/9afbb347-3aae-4e3c-b053-89d0937d29e5
-- title:
--   HK: gen top
-- statement:
--   The HK construction uses the gen top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L189-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L189-L204

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

theorem Formalism.MainNotions.UnusedSlot33.HK.gen_top (H : Host R) (x : H.K) (hx : (x : H.E) = H.sqd) :
    IntermediateField.adjoin ℚ {x} = ⊤ := by sorry
