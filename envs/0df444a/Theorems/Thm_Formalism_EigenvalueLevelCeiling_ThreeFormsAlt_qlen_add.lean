-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_add
-- name    : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:42.735417+00:00
-- url     : https://prove2.me/theorems/24c40041-cd28-48da-a570-d6a1d93e3320
-- title:
--   Three Forms Alt: qlen add
-- statement:
--   The Three Forms Alt construction uses the qlen add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L96-L98

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.qlen_add {N M P : Submodule R W} (hNM : N ≤ M) (hMP : M ≤ P) :
    qlen P N = qlen M N + qlen P M := by sorry
