-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_span_prod
-- name    : Formalism.GradedWeylDivisibility.ldtensor_span_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:46.103589+00:00
-- url     : https://prove2.me/theorems/d90466bb-6e06-49b6-802a-fbf3603e070e
-- title:
--   Graded Weyl Divisibility: ldtensor span prod
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtensor span prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L27-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TensorBasis.lean#L27-L45

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

theorem Formalism.GradedWeylDivisibility.ldtensor_span_prod (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S]
    {k n : ℕ} {ι : S → Type*}
    (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K) (F : S → MvPolynomial (Fin k × Fin n) K)
    (hF : ∀ s, F s ∈ Submodule.span R (Set.range (b s))) :
    ∏ s, blockEmb K s (F s) ∈
      Submodule.span R (Set.range fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by sorry
