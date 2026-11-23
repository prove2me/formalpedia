-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_linInd_field
-- name    : Formalism.GradedWeylDivisibility.ldtensor_prod_linInd_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:44.361804+00:00
-- url     : https://prove2.me/theorems/cd4d96fd-601a-42bb-8e20-1ef509e5c160
-- title:
--   Graded Weyl Divisibility: ldtensor prod lin Ind field
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor prod lin Ind field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L128-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L128-L138

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

theorem Formalism.GradedWeylDivisibility.ldtensor_prod_linInd_field {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by sorry
