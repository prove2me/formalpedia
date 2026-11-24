-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_primitive_density_split
-- name    : Formalism.HermitianLatticeCounting.P.primitive_density_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:42.291234+00:00
-- url     : https://prove2.me/theorems/f05c08b3-2730-4df1-9788-4a409eed4cad
-- title:
--   P: primitive density split
-- statement:
--   The P construction uses the primitive density split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4536-L4536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4536-L4536

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
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.primitive_density_split : Formalism.HermitianLatticeCounting.S4.PrimDensitySplit := by sorry
