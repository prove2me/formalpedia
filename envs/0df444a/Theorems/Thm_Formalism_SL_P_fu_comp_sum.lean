-- Prove2me | Theorems.Thm_Formalism_SL_P_fu_comp_sum
-- name    : Formalism.SL.P.fu_comp_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:20.487884+00:00
-- url     : https://prove2.me/theorems/e1d322ea-53aa-4d3f-b9c6-c26d6d505eb1
-- title:
--   P: fu comp sum
-- statement:
--   The P construction uses the fu comp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/NeighbourhoodHilbertSchmidtHolds.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/NeighbourhoodHilbertSchmidtHolds.lean#L17-L21

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

theorem Formalism.SL.P.fu_comp_sum {ι M N Q : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module ℂ M] [Module ℂ N] [Module ℂ Q] (s : Finset ι) (g : N →ₗ[ℂ] Q) (f : ι → M →ₗ[ℂ] N) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by sorry
