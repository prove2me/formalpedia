-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_involution_map_linear
-- name    : Formalism.HermitianLatticeCounting.P.involution_map_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:02.695273+00:00
-- url     : https://prove2.me/theorems/0921c31c-2596-4b27-8fd4-d42250ec54cf
-- title:
--   P: involution map linear
-- statement:
--   The P construction uses the involution map linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4521-L4521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4521-L4521

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

theorem Formalism.HermitianLatticeCounting.P.involution_map_linear : Formalism.HermitianLatticeCounting.S4.TauLin := by sorry
