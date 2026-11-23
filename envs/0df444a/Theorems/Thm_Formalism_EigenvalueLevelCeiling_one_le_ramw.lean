-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_le_ramw
-- name    : Formalism.EigenvalueLevelCeiling.one_le_ramw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:53.814972+00:00
-- url     : https://prove2.me/theorems/9260938a-3e18-4f09-b309-864031758fe0
-- title:
--   Eigenvalue Level Ceiling: one le ramw
-- statement:
--   The Eigenvalue Level Ceiling construction uses the one le ramw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L44-L51

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

theorem Formalism.EigenvalueLevelCeiling.one_le_ramw (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ ramw w := by sorry
