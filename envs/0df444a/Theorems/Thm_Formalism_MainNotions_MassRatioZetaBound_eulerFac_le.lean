-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_eulerFac_le
-- name    : Formalism.MainNotions.MassRatioZetaBound.eulerFac_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:00.683801+00:00
-- url     : https://prove2.me/theorems/0cc3c256-90c7-4005-baf4-d4b648537d90
-- title:
--   Mass Ratio Zeta Bound: euler Fac le
-- statement:
--   The Mass Ratio Zeta Bound construction uses the euler Fac le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L138-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L138-L187

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

theorem Formalism.MainNotions.MassRatioZetaBound.eulerFac_le [StarRing K] {M : ℕ} (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hN : 2 ≤ Ideal.absNorm P) :
    0 < Formalism.HermitianLatticesTheory.eulerFac K M P ∧
      Formalism.HermitianLatticesTheory.eulerFac K M P ≤ Real.exp (2 * (1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by sorry
