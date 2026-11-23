-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_conjPl
-- name    : Formalism.EigenvalueLevelCeiling.plc_conjPl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:41.989851+00:00
-- url     : https://prove2.me/theorems/05449deb-97c1-4447-ab6f-44fa0b385f81
-- title:
--   Eigenvalue Level Ceiling: plc conj Pl
-- statement:
--   The Eigenvalue Level Ceiling construction uses the plc conj Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L53-L60

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

theorem Formalism.EigenvalueLevelCeiling.plc_conjPl (w : HeightOneSpectrum (𝓞 K)) : plc (conjPl w) = plc w := by sorry
