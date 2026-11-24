-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_glue_injective
-- name    : Formalism.GradedWeylDivisibility.ldtensor_glue_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:08.340824+00:00
-- url     : https://prove2.me/theorems/9210a91e-ca3e-47fc-bc49-3df1a04063f2
-- title:
--   Graded Weyl Divisibility: ldtensor glue injective
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor glue injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L61-L67

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

theorem Formalism.GradedWeylDivisibility.ldtensor_glue_injective :
    Function.Injective (fun α : S → (Fin k × Fin n →₀ ℕ) => ∑ t, (α t).mapDomain (Prod.mk t)) := by sorry
