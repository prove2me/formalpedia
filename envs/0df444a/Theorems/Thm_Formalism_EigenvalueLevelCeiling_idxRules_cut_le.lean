-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_cut_le
-- name    : Formalism.EigenvalueLevelCeiling.idxRules_cut_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:12.337103+00:00
-- url     : https://prove2.me/theorems/d8e71ed1-7439-48c7-a515-29b1a6ae41b2
-- title:
--   Eigenvalue Level Ceiling: idx Rules cut le
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Rules cut le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L217-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L217-L243

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

theorem Formalism.EigenvalueLevelCeiling.idxRules_cut_le (p : Ideal R) [p.IsPrime] (W' : Submodule K V) (A B : Submodule R V)
    (hfin : Module.length R (↥(localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype) ≠ ⊤) :
    locLen p (A ⊓ W'.restrictScalars R) (B ⊓ W'.restrictScalars R) ≤ locLen p A B := by sorry
