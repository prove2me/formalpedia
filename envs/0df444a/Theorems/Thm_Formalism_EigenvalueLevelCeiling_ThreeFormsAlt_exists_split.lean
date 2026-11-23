-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_exists_split
-- name    : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.exists_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:54.504833+00:00
-- url     : https://prove2.me/theorems/765980c9-8498-46ae-8816-adb969ecd331
-- title:
--   Three Forms Alt: exists split
-- statement:
--   The Three Forms Alt construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L359-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L359-L382

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.exists_split (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (hA : A.FG)
    (hBA : B ≤ A) {a : K} (ha : a ≠ 0) (hav : a ∈ OO w) :
    ∃ W : Submodule K Z,
      localization₂ w.asIdeal A ≤
        cut W (localization₂ w.asIdeal A) ⊔ (localization₂ w.asIdeal A ⊓ sc a⁻¹ (localization₂ w.asIdeal B)) ∧
      cut W (sc a⁻¹ (localization₂ w.asIdeal B)) ≤ localization₂ w.asIdeal A := by sorry
