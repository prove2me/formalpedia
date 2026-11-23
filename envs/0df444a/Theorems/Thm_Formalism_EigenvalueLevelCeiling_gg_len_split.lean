-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_len_split
-- name    : Formalism.EigenvalueLevelCeiling.gg_len_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:24.586087+00:00
-- url     : https://prove2.me/theorems/535e9e9c-92f5-4e7b-a98f-a1928d8c5490
-- title:
--   Eigenvalue Level Ceiling: gg len split
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg len split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L49-L53

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]

theorem Formalism.EigenvalueLevelCeiling.gg_len_split (f : Y →ₗ[R] Y) :
    Module.length R Y =
      Module.length R (LinearMap.range f) + Module.length R (Y ⧸ LinearMap.range f) := by sorry
