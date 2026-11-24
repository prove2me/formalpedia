-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_glue_apply
-- name    : Formalism.GradedWeylDivisibility.ldtensor_glue_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:59.740789+00:00
-- url     : https://prove2.me/theorems/b1590710-a224-4086-920f-3401228e3444
-- title:
--   Graded Weyl Divisibility: ldtensor glue apply
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor glue apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L51-L59

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem Formalism.GradedWeylDivisibility.ldtensor_glue_apply (α : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    (∑ t, (α t).mapDomain (Prod.mk t)) (s, v) = α s v := by sorry
