-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_span_le
-- name    : Formalism.MainNotions.UnusedSlot33.HK.span_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:30:44.973001+00:00
-- url     : https://prove2.me/theorems/a5de489c-153f-4adc-9769-de758bb73053
-- title:
--   HK: span le
-- statement:
--   The HK construction uses the span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L300-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L300-L327

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

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

theorem Formalism.MainNotions.UnusedSlot33.HK.span_le (cc : Ideal (𝓞 H.K)) :
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} ≤
      Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
        (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc) := by sorry
