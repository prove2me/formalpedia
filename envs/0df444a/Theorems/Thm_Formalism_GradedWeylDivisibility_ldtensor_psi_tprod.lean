-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_psi_tprod
-- name    : Formalism.GradedWeylDivisibility.ldtensor_psi_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:46.772884+00:00
-- url     : https://prove2.me/theorems/47af751d-9c27-4675-bcf2-2290c616e0ec
-- title:
--   Graded Weyl Divisibility: ldtensor psi tprod
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor psi tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L78-L82

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

theorem Formalism.GradedWeylDivisibility.ldtensor_psi_tprod (F : S → MvPolynomial (Fin k × Fin n) K) :
    ldtensor_psi K (tprod K F) = ∏ s, blockEmb K s (F s) := by sorry
