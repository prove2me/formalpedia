-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_extend_family
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.extend_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:23.965699+00:00
-- url     : https://prove2.me/theorems/67c03f3f-30a3-4862-88d3-7728518235eb
-- title:
--   S4aux: extend family
-- statement:
--   The S4aux construction uses the extend family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3448-L3484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3448-L3484

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)

theorem Formalism.HermitianLatticeCounting.P.S4aux.extend_family (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (u : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (u i) (u j) = 0) (hunit : ∀ i, IsUnit (h (u i) (u i))) (r : ℕ)
    (hr : Fintype.card κ + r ≤ Module.finrank O abelian₂) :
    ∃ t : Fin r → abelian₂, (∀ i j, h (t i) (u j) = 0) ∧ (∀ i j, i ≠ j → h (t i) (t j) = 0) ∧
      ∀ i, IsUnit (h (t i) (t i)) := by sorry
