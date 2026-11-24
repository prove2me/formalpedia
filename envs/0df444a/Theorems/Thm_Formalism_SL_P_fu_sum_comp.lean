-- Prove2me | Theorems.Thm_Formalism_SL_P_fu_sum_comp
-- name    : Formalism.SL.P.fu_sum_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:21.041909+00:00
-- url     : https://prove2.me/theorems/91a1c248-9b34-4828-a646-d18753ef5b0c
-- title:
--   P: fu sum comp
-- statement:
--   The P construction uses the fu sum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/NeighbourhoodHilbertSchmidtHolds.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/NeighbourhoodHilbertSchmidtHolds.lean#L11-L15

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementFU
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_NeighbourhoodHilbertSchmidtHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.SL Formalism.SL.P
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.SL.FU
open scoped InnerProductSpace ComplexConjugate

theorem Formalism.SL.P.fu_sum_comp {ι M N Q : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (f : ι → N →ₗ[ℂ] Q) (g : M →ₗ[ℂ] N) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by sorry
