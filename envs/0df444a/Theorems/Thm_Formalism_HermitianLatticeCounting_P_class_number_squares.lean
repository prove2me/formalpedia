-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_class_number_squares
-- name    : Formalism.HermitianLatticeCounting.P.class_number_squares
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:46.075845+00:00
-- url     : https://prove2.me/theorems/a91fbac8-0957-438d-8956-2033497ef3cf
-- title:
--   P: class number squares
-- statement:
--   The P construction uses the class number squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4512-L4512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean#L4512-L4512

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

theorem Formalism.HermitianLatticeCounting.P.class_number_squares : Formalism.HermitianLatticeCounting.S4.ClassSquares := by sorry
