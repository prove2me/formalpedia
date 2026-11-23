-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_mem
-- name    : Formalism.EigenvalueLevelCeiling.plc_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:38.716289+00:00
-- url     : https://prove2.me/theorems/68d99021-0c5a-4ec3-8e1a-75691d76e30e
-- title:
--   Eigenvalue Level Ceiling: plc mem
-- statement:
--   The Eigenvalue Level Ceiling construction uses the plc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/RamBasic.lean#L27-L30

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

theorem Formalism.EigenvalueLevelCeiling.plc_mem (w : HeightOneSpectrum (𝓞 K)) : ((plc w : ℕ) : 𝓞 K) ∈ w.asIdeal := by sorry
