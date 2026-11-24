-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_span_orthogonal_unit_basis_eq_top
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.span_orthogonal_unit_basis_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:29.314821+00:00
-- url     : https://prove2.me/theorems/8092dfce-349f-4f05-9041-8ff504517bdc
-- title:
--   S4aux: span orthogonal unit basis eq top
-- statement:
--   The S4aux construction uses the span orthogonal unit basis eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3487-L3529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L3487-L3529

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
omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o]

theorem Formalism.HermitianLatticeCounting.P.S4aux.span_orthogonal_unit_basis_eq_top (v : Module.Free.ChooseBasisIndex O abelian₂ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i))) :
    Submodule.span O (Set.range v) = ⊤ := by sorry
