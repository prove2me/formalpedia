-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_act_unit_pi0_eq_mul_padic
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.act_unit_pi0_eq_mul_padic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:31.957789+00:00
-- url     : https://prove2.me/theorems/4b377869-e221-4017-a795-12eae2d43c88
-- title:
--   Height Descent Minors: act unit pi0 eq mul padic
-- statement:
--   The Height Descent Minors construction uses the act unit pi0 eq mul padic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1216-L1310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1216-L1310

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.HeightDescentMinors.act_unit_pi0_eq_mul_padic (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hi : DivisibilityInvariant) (hf : RootsOfUnityInvariants) (h4 : R4)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (u c : ℤ_[l]) (hu : u = 1 + (l : ℤ_[l]) * c) :
    ∃ un : ℤ_[l]⟦X⟧,
      act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * (1 + inc l ℤ_[l] un * q0 l ℤ_[l]) ∧
      ∃ e : ℤ_[l], constantCoeff un = c + (l : ℤ_[l]) * e := by sorry
