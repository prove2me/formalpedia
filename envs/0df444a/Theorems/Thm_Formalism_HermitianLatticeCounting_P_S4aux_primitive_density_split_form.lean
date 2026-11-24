-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_primitive_density_split_form
-- name    : Formalism.HermitianLatticeCounting.P.S4aux.primitive_density_split_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:52.887743+00:00
-- url     : https://prove2.me/theorems/a69d4691-2b54-44e1-8ae7-90b16df1a54b
-- title:
--   S4aux: primitive density split form
-- statement:
--   The S4aux construction uses the primitive density split form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2509-L2600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L2509-L2600

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

theorem Formalism.HermitianLatticeCounting.P.S4aux.primitive_density_split_form : PrimDensitySplitForm := by sorry
