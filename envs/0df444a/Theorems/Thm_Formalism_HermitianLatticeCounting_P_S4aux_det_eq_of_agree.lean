-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_eq_of_agree
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.det_eq_of_agree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:31:28.023797+00:00
-- url     : https://prove2.me/theorems/c3c38a46-15e4-4288-bbf4-c50fe828742f
-- title:
--   S4aux: det eq of agree
-- statement:
--   The S4aux construction uses the det eq of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4222-L4234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4222-L4234

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.det_eq_of_agree {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (f g : V →ₗ[F] V) (hW : ∀ x ∈ W, g x ∈ W) (hfW : ∀ x ∈ W, f x = g x)
    (hfg : ∀ x, f x - g x ∈ W) : LinearMap.det f = LinearMap.det g := by sorry
