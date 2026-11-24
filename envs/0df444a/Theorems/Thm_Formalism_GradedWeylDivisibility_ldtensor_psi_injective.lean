-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_psi_injective
-- name    : Formalism.GradedWeylDivisibility.ldtensor_psi_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:57.837431+00:00
-- url     : https://prove2.me/theorems/883fc2b0-d4e8-4283-a74f-82449dbed3d9
-- title:
--   Graded Weyl Divisibility: ldtensor psi injective
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor psi injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L84-L108

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

theorem Formalism.GradedWeylDivisibility.ldtensor_psi_injective : Function.Injective (ldtensor_psi K (S := S) (k := k) (n := n)) := by sorry
