-- Prove2me | Theorems.Thm_FockRaiseLowGrade_plus_eq
-- name    : FockRaiseLowGrade.plus_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:29.782103+00:00
-- url     : https://prove2.me/theorems/ee970b08-3ad9-4a15-944e-ec04d0a75883
-- title:
--   Fock Raise Low Grade: plus eq
-- statement:
--   The Fock Raise Low Grade construction uses the plus eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/RaisingLoweringSplit.lean#L38-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowGrade
open MvPolynomial FockH1Action
variable {σ : Type*}

theorem FockRaiseLowGrade.plus_eq (R L : Module.End ℂ (MvPolynomial σ ℂ))
    (hR : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → R P ∈ homog σ (d + 2))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : plusPart (R + L) P = R P := by sorry
