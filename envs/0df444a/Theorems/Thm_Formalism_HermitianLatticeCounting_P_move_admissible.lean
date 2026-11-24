-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_admissible
-- name    : Formalism.HermitianLatticeCounting.P.move_admissible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:38:04.391973+00:00
-- url     : https://prove2.me/theorems/c35891a4-4f17-4c21-bbf3-7a6093e8b2d1
-- title:
--   P: move admissible
-- statement:
--   The P construction uses the move admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4529-L4529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4529-L4529

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

theorem Formalism.HermitianLatticeCounting.P.move_admissible : Formalism.HermitianLatticeCounting.S4.MoveAdm := by sorry
