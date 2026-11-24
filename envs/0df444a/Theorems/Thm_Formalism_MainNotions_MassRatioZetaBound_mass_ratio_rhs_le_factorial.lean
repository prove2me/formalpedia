-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_mass_ratio_rhs_le_factorial
-- name    : Formalism.MainNotions.MassRatioZetaBound.mass_ratio_rhs_le_factorial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:41.894957+00:00
-- url     : https://prove2.me/theorems/b2ef20de-362a-40e7-b942-959cae60a571
-- title:
--   Mass Ratio Zeta Bound: mass ratio rhs le factorial
-- statement:
--   The Mass Ratio Zeta Bound construction uses the mass ratio rhs le factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L223-L238

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]

theorem Formalism.MainNotions.MassRatioZetaBound.mass_ratio_rhs_le_factorial [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤
      ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by sorry
