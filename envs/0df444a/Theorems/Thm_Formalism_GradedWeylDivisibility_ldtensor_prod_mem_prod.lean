-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_mem_prod
-- name    : Formalism.GradedWeylDivisibility.ldtensor_prod_mem_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:59.628322+00:00
-- url     : https://prove2.me/theorems/5561469e-e282-4e0c-bce3-e77d6f6d944a
-- title:
--   Graded Weyl Divisibility: ldtensor prod mem prod
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor prod mem prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L13-L25

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

theorem Formalism.GradedWeylDivisibility.ldtensor_prod_mem_prod {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {S : Type*}
    (T : Finset S) (N : S → Submodule R A) (x : S → A) (hx : ∀ s ∈ T, x s ∈ N s) :
    ∏ s ∈ T, x s ∈ ∏ s ∈ T, N s := by sorry
