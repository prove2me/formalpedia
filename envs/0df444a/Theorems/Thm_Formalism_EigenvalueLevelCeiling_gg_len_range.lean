-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_gg_len_range
-- name    : Formalism.EigenvalueLevelCeiling.gg_len_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:21.456674+00:00
-- url     : https://prove2.me/theorems/7f97591d-381b-4b06-b0c5-e9c8a3692f75
-- title:
--   Eigenvalue Level Ceiling: gg len range
-- statement:
--   The Eigenvalue Level Ceiling construction uses the gg len range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L19-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean#L19-L47

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

theorem Formalism.EigenvalueLevelCeiling.gg_len_range {ι : Type*} [Fintype ι] [DecidableEq ι] (n : R) (s : ι → Y →ₗ[R] Q)
    (t : ι → Q →ₗ[R] Y) (hts : ∀ i j y, t i (s j y) = if i = j then n • y else 0) :
    (Fintype.card ι : ℕ∞) * Module.length R (LinearMap.range (n • (LinearMap.id : Y →ₗ[R] Y))) ≤
      Module.length R Q := by sorry
