-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_isLocalHom_of_map_eq_pow
-- name    : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.isLocalHom_of_map_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:28:12.072287+00:00
-- url     : https://prove2.me/theorems/fc31c0be-ac73-4bce-b7cc-28db1fb4f496
-- title:
--   Three Forms Alt: is Local Hom of map eq pow
-- statement:
--   The Three Forms Alt construction uses the is Local Hom of map eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L482-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean#L482-L491

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
open IsLocalRing

theorem Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.isLocalHom_of_map_eq_pow (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O']
    [IsLocalRing O'] [Algebra O O'] (e : ℕ) (he : e ≠ 0)
    (h : Ideal.map (algebraMap O O') (maximalIdeal O) = maximalIdeal O' ^ e) :
    IsLocalHom (algebraMap O O') := by sorry
