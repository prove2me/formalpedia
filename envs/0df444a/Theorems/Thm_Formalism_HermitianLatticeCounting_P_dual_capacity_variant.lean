-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_capacity_variant
-- name    : Formalism.HermitianLatticeCounting.P.dual_capacity_variant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:37.155786+00:00
-- url     : https://prove2.me/theorems/5468c868-e9ed-4cbe-8be6-9db00d212387
-- title:
--   P: dual capacity variant
-- statement:
--   The P construction uses the dual capacity variant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4531-L4531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4531-L4531

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

theorem Formalism.HermitianLatticeCounting.P.dual_capacity_variant : Formalism.HermitianLatticeCounting.S4.DualCapV := by sorry
