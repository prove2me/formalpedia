-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_sum_lw_vw_natCast_le
-- name    : Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:12.013343+00:00
-- url     : https://prove2.me/theorems/b69f7626-efd9-4dce-b26e-f03af13f982b
-- title:
--   Eigenvalue Level Ceiling: sum lw vw nat Cast le
-- statement:
--   The Eigenvalue Level Ceiling construction uses the sum lw vw nat Cast le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L66-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L66-L152

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ) := by sorry
