-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_monomial
-- name    : Formalism.GradedWeylDivisibility.ldtensor_prod_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:00.043797+00:00
-- url     : https://prove2.me/theorems/7fe101b5-defa-4c23-b429-d6c148b42326
-- title:
--   Graded Weyl Divisibility: ldtensor prod monomial
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor prod monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L69-L72

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

theorem Formalism.GradedWeylDivisibility.ldtensor_prod_monomial (α : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ s, blockEmb K s (monomial (α s) (1 : K)) = monomial (∑ t, (α t).mapDomain (Prod.mk t)) 1 := by sorry
