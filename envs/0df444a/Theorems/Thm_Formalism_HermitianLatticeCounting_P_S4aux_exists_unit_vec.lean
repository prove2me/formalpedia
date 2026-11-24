-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_unit_vec
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.exists_unit_vec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:23.791936+00:00
-- url     : https://prove2.me/theorems/54e3a9e6-bba2-4b08-b227-8ccaa0007843
-- title:
--   S4aux: exists unit vec
-- statement:
--   The S4aux construction uses the exists unit vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3404-L3408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3404-L3408

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.exists_unit_vec (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by sorry
