-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_preserves_weight
-- name    : Formalism.HermitianLatticeCounting.P.move_preserves_weight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:03.849653+00:00
-- url     : https://prove2.me/theorems/5aeff3d1-16ff-4b8c-b000-519f8dbc298f
-- title:
--   P: move preserves weight
-- statement:
--   The P construction uses the move preserves weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4484-L4484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4484-L4484

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

theorem Formalism.HermitianLatticeCounting.P.move_preserves_weight : Formalism.HermitianLatticeCounting.S4.MoveWeight := by sorry
