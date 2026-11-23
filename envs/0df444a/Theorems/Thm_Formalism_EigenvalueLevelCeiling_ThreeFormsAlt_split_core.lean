-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_split_core
-- name    : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.split_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:34.241364+00:00
-- url     : https://prove2.me/theorems/f82893a4-f0e6-4413-a0a5-003a5c0d1811
-- title:
--   Three Forms Alt: split core
-- statement:
--   The Three Forms Alt construction uses the split core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L268-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L268-L277

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
variable {O K Z : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup Z] [Module K Z] [Module O Z]
  [IsScalarTower O K Z]

theorem Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.split_core (N NB : Submodule O Z) (hfg : N.FG) (hle : NB ≤ N) (a : O) (ha : a ≠ 0) :
    ∃ W : Submodule K Z,
      (∀ x ∈ N, ∃ y ∈ N, ∃ t ∈ N, y ∈ W ∧ a • t ∈ NB ∧ x = y + t) ∧
      (∀ x ∈ W, a • x ∈ NB → x ∈ N) := by sorry
